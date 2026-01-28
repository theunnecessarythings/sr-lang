const std = @import("std");

const c = @cImport({
    @cInclude("stdlib.h");
    @cInclude("string.h");
    @cInclude("unistd.h");
});

const CUresult = i32;
const CUmodule = ?*anyopaque;
const CUfunction = ?*anyopaque;

extern fn cuModuleLoad(module: *CUmodule, fname: [*]const u8) callconv(.c) CUresult;
extern fn cuModuleGetFunction(hfunc: *CUfunction, hmod: CUmodule, name: [*]const u8) callconv(.c) CUresult;
extern fn cuLaunchKernel(
    f: CUfunction,
    grid_dim_x: i32,
    grid_dim_y: i32,
    grid_dim_z: i32,
    block_dim_x: i32,
    block_dim_y: i32,
    block_dim_z: i32,
    shared_mem_bytes: i32,
    hstream: ?*anyopaque,
    kernel_params: ?**anyopaque,
    extra: ?**anyopaque,
) callconv(.c) CUresult;

const TritonEntry = struct { mod: CUmodule, func: CUfunction, mtime: i128 };
var triton_cache: ?std.StringHashMap(TritonEntry) = null;
var triton_cache_mutex = std.Thread.Mutex{};

fn tritonCache() *std.StringHashMap(TritonEntry) {
    if (triton_cache == null) {
        triton_cache = std.StringHashMap(TritonEntry).init(std.heap.c_allocator);
    }
    return &triton_cache.?;
}

fn logMsg(msg: []const u8) void {
    if (msg.len == 0) return;
    _ = c.write(2, @ptrCast(msg.ptr), msg.len);
}

fn logErr(prefix: []const u8, code: i32, name: []const u8) void {
    var buf: [256]u8 = undefined;
    const slice = std.fmt.bufPrint(&buf, "{s} (code={d}) for {s}\n", .{ prefix, code, name }) catch return;
    logMsg(slice);
}

fn logInfo(prefix: []const u8, name: []const u8) void {
    var buf: [256]u8 = undefined;
    const slice = std.fmt.bufPrint(&buf, "{s} for {s}\n", .{ prefix, name }) catch return;
    logMsg(slice);
}

fn fileMtime(path: []const u8) i128 {
    const st = std.fs.cwd().statFile(path) catch return 0;
    return @intCast(st.mtime);
}

/// Launch a Triton kernel with runtime caching of module/function.
pub export fn rt_triton_launch(
    kernel_name_ptr: [*]const u8,
    kernel_name_len: usize,
    kernel_params: ?**anyopaque,
    grid_x: i32,
    grid_y: i32,
    grid_z: i32,
    block_x: i32,
    block_y: i32,
    block_z: i32,
    shared_mem_bytes: i32,
    stream: ?*anyopaque,
) callconv(.c) i32 {
    if (kernel_name_len == 0) return -1;

    const name = kernel_name_ptr[0..kernel_name_len];
    const no_cache = blk: {
        const env = c.getenv("SR_TRITON_NOCACHE");
        if (env == null) break :blk false;
        const v = env.?;
        if (v.* == 0) break :blk false;
        if (v.* == '0') break :blk false;
        break :blk true;
    };
    const reload_cache = blk: {
        const env = c.getenv("SR_TRITON_RELOAD");
        if (env == null) break :blk false;
        const v = env.?;
        if (v.* == 0) break :blk false;
        if (v.* == '0') break :blk false;
        break :blk true;
    };

    triton_cache_mutex.lock();
    defer triton_cache_mutex.unlock();

    const cache = tritonCache();
    if (!no_cache and !reload_cache) {
        if (cache.get(name)) |entry| {
            const res = cuLaunchKernel(entry.func, grid_x, grid_y, grid_z, block_x, block_y, block_z, shared_mem_bytes, stream, kernel_params, null);
            if (res != 0) logErr("rt_triton_launch: cuLaunchKernel failed", res, name);
            return res;
        }
    }

    var name_buf: [256]u8 = undefined;
    var name_z: []u8 = &.{};
    if (kernel_name_len + 1 <= name_buf.len) {
        name_z = name_buf[0 .. kernel_name_len + 1];
        std.mem.copyForwards(u8, name_z[0..kernel_name_len], name);
        name_z[kernel_name_len] = 0;
    } else {
        name_z = std.heap.c_allocator.alloc(u8, kernel_name_len + 1) catch return -1;
        std.mem.copyForwards(u8, name_z[0..kernel_name_len], name);
        name_z[kernel_name_len] = 0;
    }

    const path_len = "out/triton_kernels/".len + kernel_name_len + ".ptx".len;
    var path_buf: [512]u8 = undefined;
    var path_z: []u8 = &.{};
    if (path_len + 1 <= path_buf.len) {
        const slice = std.fmt.bufPrint(&path_buf, "out/triton_kernels/{s}.ptx", .{name}) catch return -1;
        path_z = path_buf[0 .. slice.len + 1];
        path_z[slice.len] = 0;
    } else {
        path_z = std.heap.c_allocator.alloc(u8, path_len + 1) catch return -1;
        const slice = std.fmt.bufPrint(path_z[0..path_len], "out/triton_kernels/{s}.ptx", .{name}) catch return -1;
        path_z[slice.len] = 0;
    }

    const path_slice = path_z[0..path_len];

    if (!no_cache and reload_cache) {
        if (cache.get(name)) |entry| {
            const mt = fileMtime(path_slice);
            if (mt != 0 and mt == entry.mtime) {
                const res = cuLaunchKernel(entry.func, grid_x, grid_y, grid_z, block_x, block_y, block_z, shared_mem_bytes, stream, kernel_params, null);
                if (res != 0) logErr("rt_triton_launch: cuLaunchKernel failed", res, name);
                return res;
            }
            logInfo("rt_triton_launch: reloading PTX", name);
        }
    }

    var mod: CUmodule = null;
    var res = cuModuleLoad(&mod, path_z.ptr);
    if (res != 0) {
        logErr("rt_triton_launch: cuModuleLoad failed", res, name);
        return res;
    }

    var func: CUfunction = null;
    res = cuModuleGetFunction(&func, mod, name_z.ptr);
    if (res != 0) {
        logErr("rt_triton_launch: cuModuleGetFunction failed", res, name);
        return res;
    }

    if (!no_cache) {
        const key = std.heap.c_allocator.dupe(u8, name) catch return res;
        const mt = fileMtime(path_slice);
        _ = cache.put(key, .{ .mod = mod, .func = func, .mtime = mt }) catch {};
    }

    const launch_res = cuLaunchKernel(func, grid_x, grid_y, grid_z, block_x, block_y, block_z, shared_mem_bytes, stream, kernel_params, null);
    if (launch_res != 0) logErr("rt_triton_launch: cuLaunchKernel failed", launch_res, name);
    return launch_res;
}
