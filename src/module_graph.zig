const std = @import("std");
const cst_mod = @import("cst.zig");
const ast_mod = @import("ast.zig");
const tir_mod = @import("tir.zig");
const types = @import("types.zig");
const package_graph = @import("package/graph.zig");
const discovery = @import("package/discovery.zig");

pub const PackageId = package_graph.PackageId;
pub const PackageInfo = package_graph.PackageInfo;
pub const ModuleMatch = package_graph.ModuleMatch;
const PreludeImport = package_graph.PackageInfo.PreludeImport;

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
    packages: package_graph.PackageGraph,
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

pub const prelude_alias_prefix = "$__sr_prelude";

pub const PreludeSpec = struct {
    path: []const u8,
    reexport: package_graph.PreludeReexportConfig,
};

const std_io_prelude_symbols = &.{
    "print",
    "print0",
    "println",
    "println0",
    "eprint0",
    "eprintln0",
    "panic",
};

const std_vendor_preludes = &[_]package_graph.PreludeConfig{
    .{ .path = "std/io", .reexport = .{ .symbols = std_io_prelude_symbols } },
};

const workspace_preludes = &[_]package_graph.PreludeConfig{
    .{ .path = "std/io", .reexport = .{ .symbols = std_io_prelude_symbols } },
};

pub fn workspacePreludeConfigs() []const package_graph.PreludeConfig {
    return workspace_preludes;
}

const default_roots = [_]package_graph.RootConfig{
    .{ .name = "std", .path = "std", .prelude_imports = std_vendor_preludes },
    .{ .name = "vendor", .path = "vendor", .prelude_imports = std_vendor_preludes },
    .{ .name = "examples", .path = "examples" },
};

    pub const Config = struct {
        roots: []const package_graph.RootConfig = &default_roots,
        discovery: discovery.Rules = .{},
    };

    pub fn init(gpa: std.mem.Allocator) ModuleGraph {
        if (std_lib_path.len == 0) {
            std_lib_path = std.fs.selfExePath(&std_lib_path_buf) catch "";
        }
        var graph = ModuleGraph{
            .gpa = gpa,
            .cache = std.StringHashMap(ModuleEntry).init(gpa),
            .in_progress = std.StringHashMap(void).init(gpa),
            .owned_type_infos = std.AutoHashMap(*types.TypeInfo, void).init(gpa),
            .packages = package_graph.PackageGraph.init(gpa),
        };
        graph.rebuildPackages() catch unreachable;
        return graph;
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
        self.packages.deinit();
    }

    pub fn setConfig(self: *ModuleGraph, cfg: Config) !void {
        self.config = cfg;
        try self.rebuildPackages();
    }

    fn rebuildPackages(self: *ModuleGraph) !void {
        try self.packages.rebuild(self.config.roots, self.config.discovery);
    }

    pub fn getPackage(self: *const ModuleGraph, id: package_graph.PackageId) ?*const package_graph.PackageInfo {
        return self.packages.get(id);
    }

    pub fn findPackage(self: *const ModuleGraph, name: []const u8) ?*const package_graph.PackageInfo {
        return self.packages.getByName(name);
    }

    pub fn matchPackageImport(self: *const ModuleGraph, import_path: []const u8) ?package_graph.PackageGraph.Match {
        return self.packages.matchImport(import_path);
    }

    pub fn findModuleByPath(self: *const ModuleGraph, canonical_path: []const u8) ?ModuleMatch {
        return self.packages.findModuleByPath(canonical_path);
    }

    fn convertPreludeReexport(re: PreludeImport.PreludeReexport) package_graph.PreludeReexportConfig {
        return switch (re) {
            .none => .none,
            .all => .all,
            .symbols => |list| .{ .symbols = list.items },
        };
    }

    pub fn collectPreludeSpecsForModule(
        self: *ModuleGraph,
        module_path: []const u8,
        out: *std.ArrayList(PreludeSpec),
    ) !void {
        if (self.findPackageForPath(module_path)) |pkg| {
            const specs = pkg.preludeSpecs();
            try out.ensureTotalCapacity(out.items.len + specs.len);
            for (specs) |prelude| {
                try out.append(.{
                    .path = std.mem.sliceToConst(prelude.path),
                    .reexport = convertPreludeReexport(prelude.reexport),
                });
            }
            return;
        }

        try out.ensureTotalCapacity(out.items.len + workspace_preludes.len);
        for (workspace_preludes) |cfg| {
            try out.append(.{ .path = cfg.path, .reexport = cfg.reexport });
        }
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

    pub const ExportLookup = struct {
        module: *ModuleEntry,
        ty: ?types.TypeId,
        found: bool,
    };

    pub fn lookupExport(
        self: *ModuleGraph,
        base_dir: []const u8,
        import_path: []const u8,
        name: []const u8,
        mode: LoadMode,
    ) !ExportLookup {
        const entry = try self.ensureModule(base_dir, import_path, mode);
        if (entry.syms.get(name)) |ty| {
            return .{ .module = entry, .ty = ty, .found = true };
        }
        return .{ .module = entry, .ty = null, .found = false };
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

    fn findPackageForPath(self: *const ModuleGraph, canonical_path: []const u8) ?*const package_graph.PackageInfo {
        if (self.packages.findModuleByPath(canonical_path)) |match| {
            return match.pkg;
        }
        var best: ?*const package_graph.PackageInfo = null;
        var best_len: usize = 0;
        for (self.packages.packages.items) |*pkg| {
            if (canonical_path.len < pkg.root_path.len) continue;
            if (!std.mem.startsWith(u8, canonical_path, pkg.root_path)) continue;
            if (canonical_path.len > pkg.root_path.len) {
                const next = canonical_path[pkg.root_path.len];
                if (next != '/' and next != std.fs.path.sep) continue;
            }
            if (pkg.root_path.len > best_len) {
                best = pkg;
                best_len = pkg.root_path.len;
            }
        }
        return best;
    }

    fn loadPreludeDependencies(
        self: *ModuleGraph,
        base_dir: []const u8,
        module_path: []const u8,
        mode: LoadMode,
        seen: *std.StringHashMap(void),
        out: *std.ArrayList(*ModuleEntry),
    ) !void {
        if (self.findPackageForPath(module_path)) |pkg| {
            for (pkg.preludeSpecs()) |prelude| {
                try self.appendPreludeDependency(base_dir, module_path, std.mem.sliceToConst(prelude.path), mode, seen, out);
            }
        } else {
            for (workspace_preludes) |cfg| {
                try self.appendPreludeDependency(base_dir, module_path, cfg.path, mode, seen, out);
            }
        }
    }

    fn appendPreludeDependency(
        self: *ModuleGraph,
        base_dir: []const u8,
        module_path: []const u8,
        import_path: []const u8,
        mode: LoadMode,
        seen: *std.StringHashMap(void),
        out: *std.ArrayList(*ModuleEntry),
    ) !void {
        const resolved = try self.resolvePath(base_dir, import_path);
        defer self.gpa.free(resolved);
        if (std.mem.eql(u8, resolved, module_path)) return;
        if ((try seen.getOrPut(import_path)).found_existing) return;
        const entry = try self.ensureModule(base_dir, import_path, mode);
        try out.append(entry);
    }

    pub fn loadDependencies(
        self: *ModuleGraph,
        base_dir: []const u8,
        module_path: []const u8,
        ast: *const ast_mod.Ast,
        mode: LoadMode,
        out: *std.ArrayList(*ModuleEntry),
    ) !void {
        var seen = std.StringHashMap(void).init(self.gpa);
        defer seen.deinit();

        try self.loadPreludeDependencies(base_dir, module_path, mode, &seen, out);

        var imports: std.ArrayList([]const u8) = .empty;
        defer {
            for (imports.items) |imp| self.gpa.free(imp);
            imports.deinit(self.gpa);
        }

        try self.collectImportsFromAst(ast, &imports);

        for (imports.items) |imp| {
            if ((try seen.getOrPut(imp)).found_existing) continue;
            const entry = try self.ensureModule(base_dir, imp, mode);
            try out.append(self.gpa, entry);
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
        const package_match = self.packages.matchImport(raw_in);
        const looks_rooted = package_match != null;

        if (package_match) |match| {
            if (match.pkg.lookup(match.remainder)) |module_info| {
                return try self.gpa.dupe(u8, module_info.path);
            }
        }

        if (is_abs or looks_rooted) {
            if (is_abs) {
                try self.config.discovery.appendImportCandidates(&candidates, self.gpa, raw_in);
            } else if (package_match) |match| {
                const package_path = try match.pkg.absolutePathFor(self.gpa, match.remainder);
                defer self.gpa.free(package_path);
                try self.config.discovery.appendImportCandidates(&candidates, self.gpa, package_path);
            }
        } else {
            if (base_dir.len == 0) {
                try self.config.discovery.appendImportCandidates(&candidates, self.gpa, raw_in);
            } else {
                const base = try std.fmt.allocPrint(self.gpa, "{s}/{s}", .{ base_dir, raw_in });
                defer self.gpa.free(base);
                try self.config.discovery.appendImportCandidates(&candidates, self.gpa, base);
            }

            for (self.packages.packages.items) |pkg| {
                const base = try std.fmt.allocPrint(self.gpa, "{s}/{s}", .{ pkg.root_path, raw_in });
                defer self.gpa.free(base);
                try self.config.discovery.appendImportCandidates(&candidates, self.gpa, base);
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
