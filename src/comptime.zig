const std = @import("std");
const Context = @import("compile.zig").Context;
const types = @import("types.zig");
const mlir = @import("mlir_bindings.zig");

pub const ComptimeApi = struct {
    context: ?*anyopaque,
    print: *const fn (context: ?*anyopaque, format: [*c]const u8, ...) callconv(.c) void,
    get_type_by_name: *const fn (context: ?*anyopaque, name: [*c]const u8) callconv(.c) u32,
    type_of: *const fn (context: ?*anyopaque, expr_id: u32) callconv(.c) u32,
};

pub const ComptimeValue = union(enum) {
    Void,
    Int: u128,
    Float: f64,
    Bool: bool,
    String: []const u8,
    Type: types.TypeId,
    MlirType: mlir.Type,
    MlirAttribute: mlir.Attribute,
    MlirModule: mlir.Module,

    pub fn destroy(self: *ComptimeValue, gpa: std.mem.Allocator) void {
        switch (self.*) {
            .String => |s| {
                gpa.free(s);
            },
            .MlirModule => |*mod| {
                mod.destroy();
            },
            else => {},
        }
        self.* = .Void;
    }
};

pub fn type_of_impl(context: ?*anyopaque, type_id_raw: u32) callconv(.c) u32 {
    const ctx: *Context = @ptrCast(@alignCast(context.?));
    const type_id = types.TypeId.fromRaw(type_id_raw);
    const kind = ctx.type_store.getKind(type_id);
    std.debug.print("comptime> type_of_impl: type_id_raw={}, kind={s}\n", .{ type_id_raw, @tagName(kind) });
    return @intFromEnum(kind);
}

pub fn comptime_print_impl(context: ?*anyopaque, format: [*c]const u8, ...) callconv(.c) void {
    _ = context;
    std.debug.print("comptime> {s}\n", .{@as([]const u8, std.mem.sliceTo(format, 0))});
}

pub fn get_type_by_name_impl(context: ?*anyopaque, name: [*c]const u8) callconv(.c) u32 {
    const ctx: *Context = @ptrCast(@alignCast(context.?));
    const name_slice = std.mem.sliceTo(name, 0);
    const ts = ctx.type_store;

    if (std.mem.eql(u8, name_slice, "bool")) return ts.tBool().toRaw();
    if (std.mem.eql(u8, name_slice, "i8")) return ts.tI8().toRaw();
    if (std.mem.eql(u8, name_slice, "i16")) return ts.tI16().toRaw();
    if (std.mem.eql(u8, name_slice, "i32")) return ts.tI32().toRaw();
    if (std.mem.eql(u8, name_slice, "i64")) return ts.tI64().toRaw();
    if (std.mem.eql(u8, name_slice, "u8")) return ts.tU8().toRaw();
    if (std.mem.eql(u8, name_slice, "u16")) return ts.tU16().toRaw();
    if (std.mem.eql(u8, name_slice, "u32")) return ts.tU32().toRaw();
    if (std.mem.eql(u8, name_slice, "u64")) return ts.tU64().toRaw();
    if (std.mem.eql(u8, name_slice, "f32")) return ts.tF32().toRaw();
    if (std.mem.eql(u8, name_slice, "f64")) return ts.tF64().toRaw();
    if (std.mem.eql(u8, name_slice, "usize")) return ts.tUsize().toRaw();
    if (std.mem.eql(u8, name_slice, "char")) return ts.tU32().toRaw();
    if (std.mem.eql(u8, name_slice, "string")) return ts.tString().toRaw();
    if (std.mem.eql(u8, name_slice, "void")) return ts.tVoid().toRaw();
    if (std.mem.eql(u8, name_slice, "any")) return ts.tAny().toRaw();

    return ts.tVoid().toRaw(); // Return void if not found
}
