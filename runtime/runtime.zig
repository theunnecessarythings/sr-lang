const std = @import("std");

const c = @cImport({
    @cInclude("stdlib.h");
    @cInclude("string.h");
    @cInclude("unistd.h");
});

// Allocation API (C ABI)
pub export fn rt_alloc(size: usize) callconv(.c) ?*anyopaque {
    const raw = c.malloc(size);
    const as_any: ?*anyopaque = @ptrCast(raw);
    return as_any;
}

pub export fn rt_realloc(ptr: ?*anyopaque, new_size: usize) callconv(.c) ?*anyopaque {
    const raw = c.realloc(@ptrCast(ptr), new_size);
    const as_any: ?*anyopaque = @ptrCast(raw);
    return as_any;
}

pub export fn rt_free(ptr: ?*anyopaque) callconv(.c) void {
    if (ptr) |p| c.free(p);
}

// Memory ops (helpers for codegen)
pub export fn rt_memcpy(dst: [*]u8, src: [*]const u8, len: usize) callconv(.c) void {
    if (len == 0) return;
    _ = c.memcpy(@ptrCast(dst), @ptrCast(src), len);
}

pub export fn rt_memmove(dst: [*]u8, src: [*]const u8, len: usize) callconv(.c) void {
    if (len == 0) return;
    _ = c.memmove(@ptrCast(dst), @ptrCast(src), len);
}

pub export fn rt_memset(dst: [*]u8, value: u8, len: usize) callconv(.c) void {
    if (len == 0) return;
    _ = c.memset(@ptrCast(dst), value, len);
}

pub export fn rt_memcmp(a: [*]const u8, b: [*]const u8, len: usize) callconv(.c) i32 {
    if (len == 0) return 0;
    return @intCast(c.memcmp(@ptrCast(a), @ptrCast(b), len));
}

// I/O: print to stdout/stderr
pub export fn rt_print(ptr: [*]const u8, len: usize) callconv(.c) void {
    if (len == 0) return;
    // write(1, ptr, len);
    _ = c.write(1, @ptrCast(ptr), len);
}

pub export fn rt_eprint(ptr: [*]const u8, len: usize) callconv(.c) void {
    if (len == 0) return;
    // write(2, ptr, len);
    _ = c.write(2, @ptrCast(ptr), len);
}

// Panic: print message to stderr and abort
pub export fn rt_panic(ptr: [*]const u8, len: usize) callconv(.c) noreturn {
    if (len > 0) {
        _ = c.write(2, @ptrCast(ptr), len);
        _ = c.write(2, @ptrCast("\n"), 1);
    }
    // Abort immediately
    std.process.exit(1);
}

pub export fn rt_abort() callconv(.c) noreturn {
    std.process.exit(1);
}

pub export fn rt_assert(cond: bool, ptr: [*]const u8, len: usize) callconv(.c) void {
    if (!cond) {
        rt_panic(ptr, len);
    }
}

// Return length of a NUL-terminated C string
pub export fn rt_strlen(ptr: [*]const u8) callconv(.c) usize {
    return @intCast(c.strlen(@ptrCast(ptr)));
}

// Pointer add: returns ptr + offset (in bytes)
pub export fn rt_ptr_add(ptr: [*]u8, off: usize) callconv(.c) [*]u8 {
    const base = @intFromPtr(ptr);
    return @ptrFromInt(base + off);
}
