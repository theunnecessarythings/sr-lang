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

// ============================
// Map helpers (prototype)
// ============================
// Map layout mirrors the compiler's lowered representation:
// struct Map { len: usize, entries: DynArray<Entry> }
// where DynArray<Entry> is { ptr: *Entry, len: usize, cap: usize }.
// Entries are treated as opaque; the compiler provides `entry_size`.
const DynArray = extern struct { ptr: [*]u8, len: usize, cap: usize };
const Map = extern struct { len: usize, entries: DynArray };

/// Allocate and build a Map from a flat key/value array.
/// `kv_ptr` points to `count` consecutive entries of size `entry_size` bytes.
pub export fn builtin_map_from_kv(kv_ptr: [*]const u8, entry_size: usize, count: usize) callconv(.c) Map {
    if (count == 0 or entry_size == 0)
        return Map{ .len = 0, .entries = DynArray{ .ptr = @ptrCast(@constCast(kv_ptr)), .len = 0, .cap = 0 } };

    // Allocate space for entries
    const bytes: usize = count * entry_size;
    const raw_ptr = rt_alloc(bytes) orelse
        return Map{ .len = 0, .entries = DynArray{ .ptr = @ptrCast(@constCast(kv_ptr)), .len = 0, .cap = 0 } };
    rt_memcpy(@ptrCast(raw_ptr), @ptrCast(kv_ptr), bytes);

    return Map{
        .len = count,
        .entries = DynArray{ .ptr = @ptrCast(raw_ptr), .len = count, .cap = count },
    };
}

/// Return an empty map value.
pub export fn builtin_map_empty() callconv(.c) Map {
    return Map{ .len = 0, .entries = DynArray{ .ptr = @ptrFromInt(@as(usize, 1)), .len = 0, .cap = 0 } };
}

/// Look up `key` in `map`, inserting a new entry if missing. Returns a pointer to the value slot.
pub export fn builtin_map_get_or_insert(
    map: *Map,
    key_ptr: [*]const u8,
    key_size: usize,
    entry_size: usize,
    value_offset: usize,
) callconv(.c) [*]u8 {
    // Existing entries: linear probe for the raw key bytes
    var idx: usize = 0;
    while (idx < map.entries.len) : (idx += 1) {
        const entry_ptr: [*]u8 = @ptrFromInt(@intFromPtr(map.entries.ptr) + idx * entry_size);
        if (rt_memcmp(entry_ptr, key_ptr, key_size) == 0) {
            return @ptrFromInt(@intFromPtr(entry_ptr) + value_offset);
        }
    }

    // Need to grow by one; simple doubling strategy
    const want_len = map.entries.len + 1;
    var new_cap = if (map.entries.cap == 0) @as(usize, 4) else map.entries.cap;
    while (new_cap < want_len) new_cap *= 2;
    const new_bytes = new_cap * entry_size;
    const new_ptr_any = if (map.entries.cap == 0)
        rt_alloc(new_bytes)
    else
        rt_realloc(@ptrCast(map.entries.ptr), new_bytes);
    const new_ptr: [*]u8 = if (new_ptr_any) |p|
        @as([*]u8, @ptrCast(p))
    else
        map.entries.ptr;

    map.entries.ptr = new_ptr;
    map.entries.cap = new_cap;
    map.entries.len = want_len;
    map.len = want_len;

    // Initialize the new slot
    const entry_ptr: [*]u8 = @ptrFromInt(@intFromPtr(new_ptr) + (want_len - 1) * entry_size);
    rt_memset(entry_ptr, 0, entry_size);
    rt_memcpy(entry_ptr, key_ptr, key_size);
    return @ptrFromInt(@intFromPtr(entry_ptr) + value_offset);
}
