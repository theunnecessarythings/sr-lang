const std = @import("std");
const parser = @import("parser.zig");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const lower = @import("lower.zig");
const checker = @import("checker.zig");
const types = @import("types.zig");
const lower_tir = @import("lower_tir.zig");
const tir = @import("tir.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;

pub const ModuleEntry = struct {
    path: []u8,
    source: []u8,
    cst: cst.CST,
    ast: ast.Ast,
    type_info: *types.TypeInfo,
    tir: tir.TIR,
};

pub const ImportResolver = struct {
    gpa: std.mem.Allocator,
    diags: *Diagnostics,
    cache: std.StringHashMap(ModuleEntry),

    pub fn init(gpa: std.mem.Allocator, diags: *Diagnostics) ImportResolver {
        return .{ .gpa = gpa, .diags = diags, .cache = std.StringHashMap(ModuleEntry).init(gpa) };
    }
    pub fn deinit(self: *ImportResolver) void {
        var it = self.cache.valueIterator();
        while (it.next()) |m| {
            m.cst.deinit();
            m.ast.deinit();
            m.type_info.deinit();
            self.gpa.destroy(m.type_info);
            m.tir.deinit();
            self.gpa.free(m.path);
            self.gpa.free(m.source);
        }
        self.cache.deinit();
    }

    fn canonPath(self: *ImportResolver, base_dir: []const u8, raw: []const u8) ![]u8 {
        // If absolute, or repo-relative (std/, vendor/, examples/), use directly; else join with base_dir
        var tmp: std.ArrayList(u8) = .empty;
        errdefer tmp.deinit(self.gpa);
        if (raw.len > 0 and raw[0] == '/') {
            try tmp.appendSlice(self.gpa, raw);
        } else if (std.mem.startsWith(u8, raw, "std/") or std.mem.startsWith(u8, raw, "vendor/") or std.mem.startsWith(u8, raw, "examples/")) {
            try tmp.appendSlice(self.gpa, raw);
        } else {
            if (base_dir.len > 0) {
                try tmp.appendSlice(self.gpa, base_dir);
                if (base_dir[base_dir.len - 1] != '/') try tmp.append(self.gpa, '/');
            }
            try tmp.appendSlice(self.gpa, raw);
        }
        // Try variants: as-is, with .sr, with /main.sr, and search in std/, vendor/, examples/
        const cwd = std.fs.cwd();
        const as_is = try tmp.toOwnedSlice(self.gpa);
        if (cwd.access(as_is, .{})) |_| {
            return as_is;
        } else |_| {}
        // with .sr
        const with_ext = try std.fmt.allocPrint(self.gpa, "{s}.sr", .{as_is});
        if (cwd.access(with_ext, .{})) |_| {
            self.gpa.free(as_is);
            return with_ext;
        } else |_| self.gpa.free(with_ext);
        // with /main.sr
        const with_main = try std.fmt.allocPrint(self.gpa, "{s}/main.sr", .{as_is});
        if (cwd.access(with_main, .{})) |_| {
            self.gpa.free(as_is);
            return with_main;
        } else |_| self.gpa.free(with_main);
        // search roots
        const roots = [_][]const u8{ "std/", "vendor/", "examples/" };
        for (roots) |r| {
            const p1 = try std.fmt.allocPrint(self.gpa, "{s}{s}", .{ r, raw });
            if (cwd.access(p1, .{})) |_| {
                self.gpa.free(as_is);
                return p1;
            } else |_| self.gpa.free(p1);
            const p2 = try std.fmt.allocPrint(self.gpa, "{s}{s}.sr", .{ r, raw });
            if (cwd.access(p2, .{})) |_| {
                self.gpa.free(as_is);
                return p2;
            } else |_| self.gpa.free(p2);
            const p3 = try std.fmt.allocPrint(self.gpa, "{s}{s}/main.sr", .{ r, raw });
            if (cwd.access(p3, .{})) |_| {
                self.gpa.free(as_is);
                return p3;
            } else |_| self.gpa.free(p3);
        }
        // fallback to as_is (will likely error when opening)
        return as_is;
    }

    pub fn resolve(self: *ImportResolver, base_dir: []const u8, import_path: []const u8) !*ModuleEntry {
        const full = try self.canonPath(base_dir, import_path);
        if (self.cache.get(full)) |entry| {
            self.gpa.free(full);
            return @constCast(&entry);
        }
        // Read file
        var file = try std.fs.cwd().openFile(full, .{});
        defer file.close();
        const stat = try file.stat();
        const source = try file.readToEndAlloc(self.gpa, stat.size);
        // Null-terminate for lexer expectations
        const source0 = try self.gpa.dupeZ(u8, source);

        // Parse
        var p = parser.Parser.init(self.gpa, source0, self.diags);
        var c = try p.parse();
        // Lower
        var low = lower.Lower.init(self.gpa, &c, self.diags);
        var a = try low.run();
        // Check
        var chk = checker.Checker.init(self.gpa, self.diags, &a);
        defer chk.deinit();
        const ti = try self.gpa.create(types.TypeInfo);
        ti.* = try chk.runWithTypes();
        // Lower TIR
        var lt = lower_tir.LowerTir.init(self.gpa, ti);
        const t = try lt.run(&a);

        var entry = ModuleEntry{
            .path = full,
            .source = source0,
            .cst = c,
            .ast = a,
            .type_info = ti,
            .tir = t,
        };
        const gop = try self.cache.getOrPut(entry.path);
        if (!gop.found_existing) {
            gop.value_ptr.* = entry;
        } else {
            // already exists; clean up
            entry.cst.deinit();
            entry.ast.deinit();
            entry.type_info.deinit();
            self.gpa.destroy(entry.type_info);
            entry.tir.deinit();
            self.gpa.free(entry.path);
            self.gpa.free(entry.source);
        }
        return @constCast(gop.value_ptr);
    }

    pub fn collectImportsFromAst(self: *ImportResolver, a: *const ast.Ast, out_list: *std.ArrayList([]const u8)) !void {
        const kinds = a.exprs.index.kinds.items;
        var i: usize = 0;
        while (i < kinds.len) : (i += 1) {
            const k = kinds[i];
            if (k == .Import) {
                const ir = a.exprs.get(.Import, ast.ExprId.fromRaw(@intCast(i)));
                const ek = a.exprs.index.kinds.items[ir.expr.toRaw()];
                if (ek == .Literal) {
                    const lit = a.exprs.get(.Literal, ir.expr);
                    if (lit.kind == .string and !lit.value.isNone()) {
                        const s = a.exprs.strs.get(lit.value.unwrap());
                        // trim quotes if any
                        const imp = if (s.len >= 2 and s[0] == '"' and s[s.len - 1] == '"') s[1 .. s.len - 1] else s;
                        try out_list.append(self.gpa, try self.gpa.dupe(u8, imp));
                    }
                }
            }
        }
    }
};
