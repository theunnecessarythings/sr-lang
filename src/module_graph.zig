const std = @import("std");
const cst_mod = @import("cst.zig");
const ast_mod = @import("ast.zig");
const tir_mod = @import("tir.zig");
const types = @import("types.zig");

pub const LoadMode = enum(u4) {
    lex,
    parse,
    ast,
    check,
    tir,

    fn order(self: LoadMode) u4 {
        return @intFromEnum(self);
    }
};

pub const ModuleEntry = struct {
    path: []u8,
    stage: LoadMode = .lex,
    cst: ?cst_mod.CST = null,
    ast: ?ast_mod.Ast = null,
    tir: ?tir_mod.TIR = null,
    type_info: ?*types.TypeInfo = null,
    module_id: usize = 0,
    syms: std.StringHashMap(types.TypeId),

    pub fn init(path: []u8, gpa: std.mem.Allocator) ModuleEntry {
        return .{
            .path = path,
            .stage = .lex,
            .cst = null,
            .ast = null,
            .tir = null,
            .type_info = null,
            .module_id = 0,
            .syms = std.StringHashMap(types.TypeId).init(gpa),
        };
    }

    pub fn deinit(self: *ModuleEntry, gpa: std.mem.Allocator) void {
        if (self.cst) |*cst| {
            cst.deinit();
            self.cst = null;
        }
        if (self.ast) |*ast| {
            ast.deinit();
            self.ast = null;
        }
        if (self.tir) |*tir| {
            tir.deinit();
            self.tir = null;
        }
        if (self.type_info) |ti| {
            ti.deinit();
            gpa.destroy(ti);
            self.type_info = null;
        }
        var kit = self.syms.keyIterator();
        while (kit.next()) |k| gpa.free(k.*);
        self.syms.deinit();
        gpa.free(self.path);
    }

    pub fn astRef(self: *ModuleEntry) *ast_mod.Ast {
        std.debug.assert(self.ast != null);
        return &self.ast.?;
    }

    pub fn tirRef(self: *ModuleEntry) *tir_mod.TIR {
        std.debug.assert(self.tir != null);
        return &self.tir.?;
    }

    pub fn typeInfo(self: *ModuleEntry) *types.TypeInfo {
        std.debug.assert(self.type_info != null);
        return self.type_info.?;
    }
};

pub const ModuleGraph = struct {
    gpa: std.mem.Allocator,
    config: Config = .{},
    cache: std.StringHashMap(ModuleEntry),
    in_progress: std.StringHashMap(void),
    owned_type_infos: std.AutoHashMap(*types.TypeInfo, void),
    runner_ctx: ?*anyopaque = null,
    runner_fn: ?RunFn = null,
    runner_depth: usize = 0,

    var std_lib_path_buf: [1024]u8 = undefined;
    var std_lib_path: []u8 = &[_]u8{};

    pub const Artifacts = struct {
        cst: ?cst_mod.CST = null,
        ast: ?ast_mod.Ast = null,
        tir: ?tir_mod.TIR = null,
        type_info: ?*types.TypeInfo = null,
        module_id: usize = 0,
    };

    pub const RunFn = *const fn (ctx: *anyopaque, path: []const u8, mode: LoadMode) anyerror!Artifacts;

    pub const Config = struct {
        roots: []const []const u8 = &.{ "std", "vendor", "examples" },
        main_filenames: []const []const u8 = &.{"main.sr"},
        exts: []const []const u8 = &.{".sr"},
    };

    pub fn init(gpa: std.mem.Allocator) ModuleGraph {
        if (std_lib_path.len == 0) {
            std_lib_path = std.fs.selfExePath(&std_lib_path_buf) catch "";
        }
        return .{
            .gpa = gpa,
            .cache = std.StringHashMap(ModuleEntry).init(gpa),
            .in_progress = std.StringHashMap(void).init(gpa),
            .owned_type_infos = std.AutoHashMap(*types.TypeInfo, void).init(gpa),
        };
    }

    pub fn deinit(self: *ModuleGraph) void {
        var it = self.cache.valueIterator();
        while (it.next()) |entry| {
            self.releaseEntryArtifacts(entry);
            entry.deinit(self.gpa);
        }
        self.cache.deinit();
        self.in_progress.deinit();
        self.owned_type_infos.deinit();
    }

    pub fn setConfig(self: *ModuleGraph, cfg: Config) void {
        self.config = cfg;
    }

    pub fn enterPipeline(self: *ModuleGraph, ctx: *anyopaque, run_fn: RunFn) void {
        if (self.runner_depth == 0) {
            self.runner_ctx = ctx;
            self.runner_fn = run_fn;
        } else {
            std.debug.assert(self.runner_ctx.? == ctx);
            std.debug.assert(self.runner_fn.? == run_fn);
        }
        self.runner_depth += 1;
    }

    pub fn leavePipeline(self: *ModuleGraph, ctx: *anyopaque) void {
        if (self.runner_depth == 0) return;
        std.debug.assert(self.runner_ctx.? == ctx);
        self.runner_depth -= 1;
        if (self.runner_depth == 0) {
            self.runner_ctx = null;
            self.runner_fn = null;
        }
    }

    pub fn resolve(self: *ModuleGraph, base_dir: []const u8, import_path: []const u8, pipeline: *anyopaque) !*ModuleEntry {
        _ = pipeline;
        return self.ensureModule(base_dir, import_path, .tir);
    }

    pub fn ensureModule(self: *ModuleGraph, base_dir: []const u8, import_path: []const u8, mode: LoadMode) !*ModuleEntry {
        const abs_real = try self.resolvePath(base_dir, import_path);
        defer self.gpa.free(abs_real);

        if (self.cache.getPtr(abs_real)) |entry_ptr| {
            if (entry_ptr.stage.order() >= mode.order()) {
                return entry_ptr;
            }
            try self.upgradeEntry(entry_ptr, abs_real, mode);
            return entry_ptr;
        }

        self.in_progress.putNoClobber(abs_real, {}) catch {
            return error.CircularImport;
        };
        defer _ = self.in_progress.remove(abs_real);

        var entry = try self.createEntry(abs_real, mode);
        const gop = self.cache.getOrPut(entry.path) catch |err| {
            entry.deinit(self.gpa);
            return err;
        };
        if (gop.found_existing) {
            entry.deinit(self.gpa);
            return gop.value_ptr;
        }
        gop.value_ptr.* = entry;
        return gop.value_ptr;
    }

    pub fn ownsTypeInfo(self: *const ModuleGraph, ti: *const types.TypeInfo) bool {
        return self.owned_type_infos.contains(@constCast(ti));
    }

    pub fn collectImportsFromAst(self: *ModuleGraph, a: *const ast_mod.Ast, out_list: *std.ArrayList([]const u8)) !void {
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

    pub fn resolvePath(self: *ModuleGraph, base_dir: []const u8, raw_in: []const u8) ![]u8 {
        var candidates: std.ArrayList([]const u8) = .empty;
        defer {
            for (candidates.items) |c| self.gpa.free(c);
            candidates.deinit(self.gpa);
        }

        const is_abs = raw_in.len > 0 and (raw_in[0] == '/' or
            (raw_in.len >= 3 and raw_in[1] == ':' and (raw_in[2] == '\\' or raw_in[2] == '/')));

        const looks_rooted = blk: {
            for (self.config.roots) |r| {
                if (std.mem.startsWith(u8, raw_in, r)) break :blk true;
                const with_slash = std.fmt.allocPrint(self.gpa, "{s}/", .{r}) catch "";
                defer if (with_slash.len != 0) self.gpa.free(with_slash);
                if (with_slash.len != 0 and std.mem.startsWith(u8, raw_in, with_slash)) break :blk true;
            }
            break :blk false;
        };

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

        const cwd = std.fs.cwd();
        var i: usize = 0;
        if (std_lib_path.len == 0) {
            std_lib_path = std.fs.selfExePath(&std_lib_path_buf) catch "";
        }
        const std_lib_parent = if (std_lib_path.len >= 20)
            std_lib_path[0 .. std_lib_path.len - 20]
        else
            std_lib_path;
        var std_dir_opt: ?std.fs.Dir = std.fs.openDirAbsolute(std_lib_parent, .{}) catch null;
        defer if (std_dir_opt) |*dir| dir.close();

        while (i < candidates.items.len) : (i += 1) {
            if (cwd.access(candidates.items[i], .{})) |_| {
                const canonical = cwd.realpathAlloc(self.gpa, candidates.items[i]) catch |e| switch (e) {
                    error.FileNotFound, error.AccessDenied => continue,
                    else => return e,
                };
                return canonical;
            } else |_| {}
            if (std_dir_opt) |*dir| {
                if (dir.access(candidates.items[i], .{})) |_| {
                    const canonical = dir.realpathAlloc(self.gpa, candidates.items[i]) catch |e| switch (e) {
                        error.FileNotFound, error.AccessDenied => continue,
                        else => return e,
                    };
                    return canonical;
                } else |_| {}
            }
        }

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

    fn createEntry(self: *ModuleGraph, abs_real: []const u8, mode: LoadMode) !ModuleEntry {
        const path = try self.gpa.dupe(u8, abs_real);
        var entry = ModuleEntry.init(path, self.gpa);
        errdefer entry.deinit(self.gpa);

        const result = try self.invokeRunner(abs_real, mode);
        try self.installResult(&entry, result, mode);
        return entry;
    }

    fn upgradeEntry(self: *ModuleGraph, entry: *ModuleEntry, abs_real: []const u8, mode: LoadMode) !void {
        self.releaseEntryArtifacts(entry);
        const result = try self.invokeRunner(abs_real, mode);
        try self.installResult(entry, result, mode);
    }

    fn installResult(self: *ModuleGraph, entry: *ModuleEntry, result: Artifacts, mode: LoadMode) !void {
        entry.stage = mode;
        entry.module_id = result.module_id;

        if (result.cst) |cst| entry.cst = cst;
        if (result.ast) |ast| entry.ast = ast;
        if (result.tir) |tir| entry.tir = tir;

        if (result.type_info) |ti| {
            entry.type_info = ti;
            errdefer {
                _ = self.owned_type_infos.remove(ti);
                ti.deinit();
                self.gpa.destroy(ti);
                entry.type_info = null;
            }
            try self.owned_type_infos.put(ti, {});
        }

        if (mode.order() >= LoadMode.check.order()) {
            std.debug.assert(entry.ast != null);
            std.debug.assert(entry.type_info != null);
            self.clearExports(entry);
            try self.buildExports(&entry.syms, &entry.ast.?, entry.type_info.?);
        } else {
            self.clearExports(entry);
        }
    }

    fn releaseEntryArtifacts(self: *ModuleGraph, entry: *ModuleEntry) void {
        if (entry.cst) |*cst| {
            cst.deinit();
            entry.cst = null;
        }
        if (entry.ast) |*ast| {
            ast.deinit();
            entry.ast = null;
        }
        if (entry.tir) |*tir| {
            tir.deinit();
            entry.tir = null;
        }
        self.clearExports(entry);
        if (entry.type_info) |ti| {
            _ = self.owned_type_infos.remove(ti);
            ti.deinit();
            self.gpa.destroy(ti);
            entry.type_info = null;
        }
        entry.module_id = 0;
        entry.stage = .lex;
    }

    fn clearExports(self: *ModuleGraph, entry: *ModuleEntry) void {
        var kit = entry.syms.keyIterator();
        while (kit.next()) |k| self.gpa.free(k.*);
        entry.syms.clearRetainingCapacity();
    }

    fn invokeRunner(self: *ModuleGraph, abs_real: []const u8, mode: LoadMode) !Artifacts {
        const run_fn = self.runner_fn orelse return error.NoRunner;
        const ctx = self.runner_ctx orelse return error.NoRunner;
        return run_fn(ctx, abs_real, mode);
    }

    fn buildExports(
        self: *ModuleGraph,
        symmap: *std.StringHashMap(types.TypeId),
        a: *const ast_mod.Ast,
        ti: *const types.TypeInfo,
    ) !void {
        std.debug.assert(ti.module_id == a.module_id);
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
                    gop.value_ptr.* = tval;
                } else {
                    gop.value_ptr.* = tval;
                }
            } else {
                self.gpa.free(key);
            }
        }
    }
};

fn hasAnyExt(path: []const u8, exts: []const []const u8) bool {
    for (exts) |e| {
        if (std.mem.endsWith(u8, path, e)) return true;
    }
    return false;
}

inline fn push(list: *std.ArrayList([]const u8), gpa: std.mem.Allocator, s: []const u8) !void {
    try list.append(gpa, try gpa.dupe(u8, s));
}
