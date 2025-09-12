const std = @import("std");
const Loc = @import("lexer.zig").Token.Loc;

pub const Severity = enum { err, warning, note };

pub const Note = struct {
    loc: ?Loc = null,
    message: []const u8,
};

pub const Message = struct {
    severity: Severity,
    loc: Loc,
    message: []const u8,
    notes: std.array_list.Managed(Note),
};

pub const Diagnostics = struct {
    allocator: std.mem.Allocator,
    messages: std.array_list.Managed(Message),

    pub fn init(allocator: std.mem.Allocator) Diagnostics {
        return .{ .allocator = allocator, .messages = std.array_list.Managed(Message).init(allocator) };
    }

    pub fn deinit(self: *Diagnostics) void {
        // Free message strings and note strings
        for (self.messages.items) |*m| {
            self.allocator.free(m.message);
            for (m.notes.items) |*n| self.allocator.free(n.message);
            m.notes.deinit();
        }
        self.messages.deinit();
    }

    pub fn addError(self: *Diagnostics, loc: Loc, comptime fmt: []const u8, args: anytype) !void {
        try self.addMessage(.err, loc, fmt, args);
    }

    pub fn addWarning(self: *Diagnostics, loc: Loc, comptime fmt: []const u8, args: anytype) !void {
        try self.addMessage(.warning, loc, fmt, args);
    }

    pub fn addNote(self: *Diagnostics, loc: Loc, comptime fmt: []const u8, args: anytype) !void {
        try self.addMessage(.note, loc, fmt, args);
    }

    fn addMessage(self: *Diagnostics, sev: Severity, loc: Loc, comptime fmt: []const u8, args: anytype) !void {
        const msg = try std.fmt.allocPrint(self.allocator, fmt, args);
        const notes = std.array_list.Managed(Note).init(self.allocator);
        try self.messages.append(.{ .severity = sev, .loc = loc, .message = msg, .notes = notes });
    }

    pub fn attachNote(self: *Diagnostics, idx: usize, loc: ?Loc, comptime fmt: []const u8, args: anytype) !void {
        if (idx >= self.messages.items.len) return; // ignore out of range
        const msg = try std.fmt.allocPrint(self.allocator, fmt, args);
        try self.messages.items[idx].notes.append(.{ .loc = loc, .message = msg });
    }

    pub fn anyErrors(self: *Diagnostics) bool {
        for (self.messages.items) |m| if (m.severity == .err) return true;
        return false;
    }

    pub fn count(self: *Diagnostics) usize {
        return self.messages.items.len;
    }

    // Pretty-print diagnostics with source excerpt and caret span (unstyled)
    pub fn emit(self: *Diagnostics, source: []const u8, writer: anytype, filename: []const u8) !void {
        try self.emitStyled(source, writer, filename, true);
    }

    // Pretty-print diagnostics Rust-like with optional ANSI colors
    pub fn emitStyled(self: *Diagnostics, source: []const u8, writer: anytype, filename: []const u8, color: bool) !void {
        for (self.messages.items) |m| {
            const sev_str = switch (m.severity) {
                .err => "error",
                .warning => "warning",
                .note => "note",
            };
            const sev_col = switch (m.severity) {
                .err => Colors.red,
                .warning => Colors.yellow,
                .note => Colors.blue,
            };
            // Header: error: message
            try writer.print("{s}{s}{s}{s}: {s}{s}\n", .{
                if (color) Colors.bold else "",
                if (color) sev_col else "",
                sev_str,
                if (color) Colors.reset else "",
                if (color) Colors.bold else "",
                m.message,
            });

            // Location line
            const lc = lineCol(source, m.loc.start);
            try writer.print(" {s}--> {s}{s}{s}:{d}:{d}\n", .{
                gutterPad(0),
                if (color) Colors.cyan else "",
                filename,
                if (color) Colors.reset else "",
                lc.line + 1,
                lc.col + 1,
            });

            const line_no = lc.line + 1;
            const width = digits(line_no);
            // Gutter spacer
            try writer.print(
                " {s}{s}▌{s}\n",
                .{ gutterPad(width), if (color) Colors.cyan else "", if (color) Colors.reset else "" },
            );
            // Source line
            const line_slice = source[lc.line_start..lc.line_end];
            const num_pad = numPad(width, line_no);
            try writer.print(
                "{s}{d} {s}▌{s} {s}\n",
                .{ num_pad, line_no, Colors.cyan, Colors.reset, line_slice },
            );
            // Underline
            const caret_start = lc.col;
            const span = if (m.loc.end > m.loc.start and m.loc.end <= lc.line_end) (m.loc.end - m.loc.start) else 1;
            try writer.print(
                " {s}{s}▌{s} ",
                .{ gutterPad(width), Colors.cyan, Colors.reset },
            );
            var i: usize = 0;
            while (i < caret_start) : (i += 1) try writer.print(" ", .{});
            if (color) try writer.print("{s}", .{sev_col});
            i = 0;
            while (i < span) : (i += 1) try writer.print("^", .{});
            if (color) try writer.print("{s}", .{Colors.reset});
            try writer.print("\n", .{});

            // Notes
            for (m.notes.items) |n| {
                if (n.loc) |nl| {
                    const nlc = lineCol(source, nl.start);
                    try writer.print(" {s}= {s}note{s}: {s} (at {s}{d}:{d}{s})\n", .{
                        gutterPad(width),
                        if (color) Colors.blue else "",
                        if (color) Colors.reset else "",
                        n.message,
                        if (color) Colors.cyan else "",
                        nlc.line + 1,
                        nlc.col + 1,
                        if (color) Colors.reset else "",
                    });
                } else {
                    try writer.print(" {s}= {s}note{s}: {s}\n", .{
                        gutterPad(width),
                        if (color) Colors.blue else "",
                        if (color) Colors.reset else "",
                        n.message,
                    });
                }
            }

            try writer.print("\n", .{});
        }
        try writer.flush();
    }

    const LineCol = struct { line: usize, col: usize, line_start: usize, line_end: usize };
    fn lineCol(src: []const u8, idx: usize) LineCol {
        var i: usize = 0;
        var line: usize = 0;
        var last_nl: usize = 0;
        while (i < src.len and i < idx) : (i += 1) {
            if (src[i] == '\n') {
                line += 1;
                last_nl = i + 1;
            }
        }
        // find end of line
        var end: usize = idx;
        while (end < src.len and src[end] != '\n' and src[end] != '\r') : (end += 1) {}
        return .{ .line = line, .col = idx - last_nl, .line_start = last_nl, .line_end = end };
    }

    fn digits(n: usize) usize {
        var v: usize = n;
        var c: usize = 1;
        while (v >= 10) : (v /= 10) c += 1;
        return c;
    }

    fn gutterPad(width: usize) []const u8 {
        // Return a short run of spaces for gutter alignment (max 16)
        const max = 16;
        const n = if (width > max) max else width;
        return space_buf[0..n];
    }

    const space_buf = [_]u8{' '} ** 16;

    fn numPad(width: usize, n: usize) []const u8 {
        const d = digits(n);
        const pad = if (width > d) width - d else 0;
        return gutterPad(pad);
    }

    const Colors = struct {
        pub const reset = "\x1b[0m";
        pub const bold = "\x1b[1m";
        pub const red = "\x1b[31m";
        pub const yellow = "\x1b[33m";
        pub const blue = "\x1b[34m";
        pub const cyan = "\x1b[36m";
    };
};
