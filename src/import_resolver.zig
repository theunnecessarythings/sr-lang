const std = @import("std");

const parser = @import("parser.zig");
const cst_mod = @import("cst.zig");
const ast_mod = @import("ast.zig");
const lower = @import("lower.zig");
const checker = @import("checker.zig");
const types = @import("types.zig");
const lower_tir = @import("lower_tir.zig");
const tir_mod = @import("tir.zig");
const Pipeline = @import("pipeline.zig").Pipeline;
const Context = @import("compile.zig").Context;
const Diagnostics = @import("diagnostics.zig").Diagnostics;

pub const ModuleEntry = struct {
    /// Absolute, canonical (realpath) to the root source file of this module.
    path: []u8,

    cst: cst_mod.CST,
    ast: ast_mod.Ast,
    tir: tir_mod.TIR,

    /// Exported symbols: binding name -> TypeId (from this module's TypeStore).
    syms: std.StringHashMap(types.TypeId),

    pub fn deinit(self: *ModuleEntry, gpa: std.mem.Allocator) void {
        // The symmap keys are duped on gpa, so free them explicitly.
        var kit = self.syms.keyIterator();
        while (kit.next()) |k| gpa.free(k.*);
        self.syms.deinit();

        gpa.free(self.path);
    }
};

pub const ImportResolver = struct {
    gpa: std.mem.Allocator,

    /// Canonical absolute file path -> ModuleEntry (owned by this map).
    cache: std.StringHashMap(ModuleEntry),

    /// In-flight resolutions to prevent import cycles.
    in_progress: std.StringHashMap(void),

    config: Config,

    pub const Config = struct {
        /// Roots searched when the import is not absolute and not clearly relative.
        roots: []const []const u8 = &.{ "std", "vendor", "examples" },

        /// Candidate filenames to try when the import resolves to a directory.
        main_filenames: []const []const u8 = &.{"main.sr"},

        /// Extensions auto-appended if the import has no extension.
        exts: []const []const u8 = &.{".sr"},
    };

    pub fn init(gpa: std.mem.Allocator) ImportResolver {
        return .{
            .gpa = gpa,
            .cache = std.StringHashMap(ModuleEntry).init(gpa),
            .in_progress = std.StringHashMap(void).init(gpa),
            .config = .{},
        };
    }

    pub fn deinit(self: *ImportResolver) void {
        var it = self.cache.valueIterator();
        while (it.next()) |entry| entry.deinit(self.gpa);
        self.cache.deinit();
        self.in_progress.deinit();
    }

    pub fn setConfig(self: *ImportResolver, cfg: Config) void {
        self.config = cfg;
    }

    /// Resolve `import_path` relative to `base_dir` (the importing file’s directory).
    /// Returns a cached `ModuleEntry` pointer.
    pub fn resolve(
        self: *ImportResolver,
        base_dir: []const u8,
        import_path: []const u8,
        pipeline: *Pipeline,
    ) !*ModuleEntry {
        // 1) Canonicalize to an absolute real path (or best-effort canonical string)
        const abs_real = try self.canonPath(base_dir, import_path);
        defer self.gpa.free(abs_real);

        // 2) Cache hit?
        if (self.cache.get(abs_real)) |entry| {
            return @constCast(&entry);
        }

        // 3) Cycle check
        self.in_progress.putNoClobber(abs_real, {}) catch {
            // _ = self.diags.addError(..., .circular_import, .{}) catch {};
            return error.CircularImport;
        };
        defer _ = self.in_progress.remove(abs_real);

        var result = try pipeline.runWithImports(abs_real, &.{}, .tir);

        // 10) Build export table
        var symmap = std.StringHashMap(types.TypeId).init(self.gpa);
        try self.buildExports(&symmap, &result.ast.?, result.type_info.?);

        // 11) Install into cache
        var entry = ModuleEntry{
            .path = try self.gpa.dupe(u8, abs_real),
            .cst = result.cst.?,
            .ast = result.ast.?,
            .tir = result.tir.?,
            .syms = symmap,
        };

        const gop = try self.cache.getOrPut(entry.path);
        if (!gop.found_existing) {
            gop.value_ptr.* = entry;
            return @constCast(gop.value_ptr);
        } else {
            // Shouldn't happen (we checked earlier), but keep it safe.
            entry.deinit(self.gpa);
            return @constCast(gop.value_ptr);
        }
    }

    /// Collect raw import strings from an AST (e.g. for prefetching).
    pub fn collectImportsFromAst(self: *ImportResolver, a: *const ast_mod.Ast, out_list: *std.ArrayList([]const u8)) !void {
        for (a.exprs.Import.list.items(.expr)) |expr| {
            const ek = a.exprs.index.kinds.items[expr.toRaw()];
            if (ek != .Literal) continue;
            const lit = a.exprs.get(.Literal, expr);
            if (lit.kind == .string) {
                const sid = switch (lit.data) {
                    .string => |str_id| str_id,
                    else => continue,
                };
                const s = a.exprs.strs.get(sid);
                try out_list.append(self.gpa, try self.gpa.dupe(u8, s));
            }
        }
    }

    // ---------------- internals ----------------

    fn buildExports(
        self: *ImportResolver,
        symmap: *std.StringHashMap(types.TypeId),
        a: *const ast_mod.Ast,
        ti: *const types.TypeInfo,
    ) !void {
        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        var i: usize = 0;
        while (i < decls.len) : (i += 1) {
            const drow = a.exprs.Decl.get(decls[i]);
            if (drow.pattern.isNone()) continue;

            const pid = drow.pattern.unwrap();
            const pk = a.pats.index.kinds.items[pid.toRaw()];
            if (pk != .Binding) continue;

            const b = a.pats.get(.Binding, pid);
            const name_s = a.exprs.strs.get(b.name);
            const key = try self.gpa.dupe(u8, name_s);

            var ty_opt: ?types.TypeId = null;
            if (decls[i].toRaw() < ti.decl_types.items.len)
                ty_opt = ti.decl_types.items[decls[i].toRaw()];
            if (ty_opt == null and drow.value.toRaw() < ti.expr_types.items.len)
                ty_opt = ti.expr_types.items[drow.value.toRaw()];

            if (ty_opt) |tval| {
                const gop = try symmap.getOrPut(key);
                if (gop.found_existing) {
                    self.gpa.free(key);
                    gop.value_ptr.* = tval; // last-wins
                } else {
                    gop.value_ptr.* = tval;
                }
            } else {
                self.gpa.free(key);
            }
        }
    }

    fn hasAnyExt(path: []const u8, exts: []const []const u8) bool {
        for (exts) |e| {
            if (std.mem.endsWith(u8, path, e)) return true;
        }
        return false;
    }

    inline fn push(list: *std.ArrayList([]const u8), gpa: std.mem.Allocator, s: []const u8) !void {
        try list.append(gpa, try gpa.dupe(u8, s));
    }

    fn canonPath(self: *ImportResolver, base_dir: []const u8, raw_in: []const u8) ![]u8 {
        // Build a list of candidate paths, then pick the first that exists.
        var candidates: std.ArrayList([]const u8) = .empty;
        defer {
            for (candidates.items) |c| self.gpa.free(c);
            candidates.deinit(self.gpa);
        }

        const is_abs = raw_in.len > 0 and (raw_in[0] == '/' or
            (raw_in.len >= 3 and raw_in[1] == ':' and (raw_in[2] == '\\' or raw_in[2] == '/'))); // win compat

        const looks_rooted = blk: {
            for (self.config.roots) |r| {
                if (std.mem.startsWith(u8, raw_in, r)) break :blk true;
                const with_slash = std.fmt.allocPrint(self.gpa, "{s}/", .{r}) catch "";
                defer if (with_slash.len != 0) self.gpa.free(with_slash);
                if (with_slash.len != 0 and std.mem.startsWith(u8, raw_in, with_slash)) break :blk true;
            }
            break :blk false;
        };

        // a) absolute / rooted as given
        if (is_abs or looks_rooted) {
            try push(&candidates, self.gpa, raw_in);
            if (!hasAnyExt(raw_in, self.config.exts)) {
                for (self.config.exts) |e| {
                    const temp_str = try std.fmt.allocPrint(self.gpa, "{s}{s}", .{ raw_in, e });
                    defer self.gpa.free(temp_str);
                    try push(&candidates, self.gpa, temp_str);
                }
            }
            for (self.config.main_filenames) |mf| {
                const temp_str = try std.fmt.allocPrint(self.gpa, "{s}/{s}", .{ raw_in, mf });
                defer self.gpa.free(temp_str);
                try push(&candidates, self.gpa, temp_str);
            }
        } else {
            // b) relative to base_dir
            if (base_dir.len == 0) {
                try push(&candidates, self.gpa, raw_in);
            } else {
                const temp_str = try std.fmt.allocPrint(self.gpa, "{s}/{s}", .{ base_dir, raw_in });
                defer self.gpa.free(temp_str);
                try push(&candidates, self.gpa, temp_str);
            }

            const last = candidates.items[candidates.items.len - 1];
            if (!hasAnyExt(last, self.config.exts)) {
                for (self.config.exts) |e| {
                    const temp_str = try std.fmt.allocPrint(self.gpa, "{s}{s}", .{ last, e });
                    defer self.gpa.free(temp_str);
                    try push(&candidates, self.gpa, temp_str);
                }
            }
            for (self.config.main_filenames) |mf| {
                const temp_str = try std.fmt.allocPrint(self.gpa, "{s}/{s}", .{ last, mf });
                defer self.gpa.free(temp_str);
                try push(&candidates, self.gpa, temp_str);
            }

            // c) search roots/<raw>
            for (self.config.roots) |r| {
                const base = try std.fmt.allocPrint(self.gpa, "{s}/{s}", .{ r, raw_in });
                defer self.gpa.free(base);

                try push(&candidates, self.gpa, base);
                if (!hasAnyExt(base, self.config.exts)) {
                    for (self.config.exts) |e| {
                        const temp_str = try std.fmt.allocPrint(self.gpa, "{s}{s}", .{ base, e });
                        defer self.gpa.free(temp_str);
                        try push(&candidates, self.gpa, temp_str);
                    }
                }
                for (self.config.main_filenames) |mf| {
                    const temp_str = try std.fmt.allocPrint(self.gpa, "{s}/{s}", .{ base, mf });
                    defer self.gpa.free(temp_str);
                    try push(&candidates, self.gpa, temp_str);
                }
            }
        }

        // Pick the first that exists, then canonicalize via realpath.
        const cwd = std.fs.cwd();
        var i: usize = 0;
        while (i < candidates.items.len) : (i += 1) {
            if (cwd.access(candidates.items[i], .{})) |_| {
                const canonical = cwd.realpathAlloc(self.gpa, candidates.items[i]) catch |e| switch (e) {
                    error.FileNotFound, error.AccessDenied => continue,
                    else => return e,
                };
                return canonical;
            } else |_| {}
        }

        // If none exist, compose a stable fallback path and try to realpath it; if that fails, just return it duped.
        var tmp: std.ArrayList(u8) = .empty;
        defer tmp.deinit(self.gpa);

        if (is_abs or looks_rooted) {
            try tmp.appendSlice(self.gpa, raw_in);
        } else if (base_dir.len > 0) {
            try tmp.appendSlice(self.gpa, base_dir);
            if (base_dir[base_dir.len - 1] != '/') try tmp.append(self.gpa, '/');
            try tmp.appendSlice(self.gpa, raw_in);
        } else {
            try tmp.appendSlice(self.gpa, raw_in);
        }

        return cwd.realpathAlloc(self.gpa, tmp.items) catch |e| switch (e) {
            error.FileNotFound, error.AccessDenied => try self.gpa.dupe(u8, tmp.items),
            else => return e,
        };
    }
};
