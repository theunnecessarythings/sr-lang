const std = @import("std");
const List = std.array_list.Managed;

// Simple type arena + interning producing stable TypeId handles.

pub const TypeId = u32;

pub const TypeKind = enum(u8) {
    Void,
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    String, // convenience builtin (slice of u8)
    Ptr,
    Slice,
    Array,
    Optional,
    Tuple,
    Function,
    Struct,
};

pub const Type = union(TypeKind) {
    Void: void,
    Bool: void,
    I8: void,
    I16: void,
    I32: void,
    I64: void,
    U8: void,
    U16: void,
    U32: void,
    U64: void,
    F32: void,
    F64: void,
    String: void,
    Ptr: struct { elem: TypeId, is_const: bool = false },
    Slice: struct { elem: TypeId },
    Array: struct { elem: TypeId, len: usize },
    Optional: struct { elem: TypeId },
    Tuple: struct { elems: []const TypeId },
    Function: FnType,
    Struct: StructType,
};

pub const FnType = struct {
    params: []const TypeId,
    result: TypeId,
    is_variadic: bool = false,
};

pub const StructField = struct { name: []const u8, ty: TypeId };
pub const StructType = struct { fields: []const StructField };

pub const TypeArena = struct {
    allocator: std.mem.Allocator,
    // intern via linear scan; fine for now
    types: List(Type),

    pub fn init(allocator: std.mem.Allocator) TypeArena {
        const arena = TypeArena{ .allocator = allocator, .types = List(Type).init(allocator) };
        return arena;
    }

    pub fn deinit(self: *TypeArena) void {
        self.types.deinit();
    }

    pub fn mk(self: *TypeArena, ty: Type) !TypeId {
        // linear dedup
        for (self.types.items, 0..) |existing, idx| {
            if (typeEq(existing, ty)) return @intCast(idx);
        }
        try self.types.append(ty);
        return @intCast(self.types.items.len - 1);
    }

    pub fn get(self: *const TypeArena, id: TypeId) Type {
        return self.types.items[@intCast(id)];
    }

    pub fn fmt(self: *const TypeArena, id: TypeId, writer: anytype) !void {
        const ty = self.get(id);
        switch (ty) {
            .Void => try writer.print("void", .{}),
            .Bool => try writer.print("bool", .{}),
            .I8 => try writer.print("i8", .{}),
            .I16 => try writer.print("i16", .{}),
            .I32 => try writer.print("i32", .{}),
            .I64 => try writer.print("i64", .{}),
            .U8 => try writer.print("u8", .{}),
            .U16 => try writer.print("u16", .{}),
            .U32 => try writer.print("u32", .{}),
            .U64 => try writer.print("u64", .{}),
            .F32 => try writer.print("f32", .{}),
            .F64 => try writer.print("f64", .{}),
            .String => try writer.print("string", .{}),
            .Ptr => |p| {
                try writer.print("*", .{});
                try self.fmt(p.elem, writer);
            },
            .Slice => |s| {
                try writer.print("[]", .{});
                try self.fmt(s.elem, writer);
            },
            .Array => |a| {
                try writer.print("[{}]", .{a.len});
                try self.fmt(a.elem, writer);
            },
            .Optional => |o| {
                try writer.print("?", .{});
                try self.fmt(o.elem, writer);
            },
            .Tuple => |t| {
                try writer.print("(", .{});
                for (t.elems, 0..) |eid, i| {
                    if (i != 0) try writer.print(", ", .{});
                    try self.fmt(eid, writer);
                }
                try writer.print(")", .{});
            },
            .Function => |fnc| {
                try writer.print("fn(", .{});
                for (fnc.params, 0..) |pid, i| {
                    if (i != 0) try writer.print(", ", .{});
                    try self.fmt(pid, writer);
                }
                try writer.print(") ", .{});
                try self.fmt(fnc.result, writer);
            },
            .Struct => |st| {
                try writer.print("struct {{ ", .{});
                for (st.fields, 0..) |f, i| {
                    if (i != 0) try writer.print(", ", .{});
                    try writer.print("{s}: ", .{f.name});
                    try self.fmt(f.ty, writer);
                }
                try writer.print(" }}", .{});
            },
        }
    }
};

fn typeEq(a: Type, b: Type) bool {
    if (@as(TypeKind, a) != @as(TypeKind, b)) return false;
    return switch (a) {
        .Void, .Bool, .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .String => true,
        .Ptr => |pa| blk: {
            const pb = b.Ptr;
            break :blk pa.elem == pb.elem and pa.is_const == pb.is_const;
        },
        .Slice => |sa| sa.elem == b.Slice.elem,
        .Array => |aa| blk: {
            const ab = b.Array;
            break :blk aa.elem == ab.elem and aa.len == ab.len;
        },
        .Optional => |oa| oa.elem == b.Optional.elem,
        .Tuple => |ta| blk: {
            const tb = b.Tuple;
            if (ta.elems.len != tb.elems.len) break :blk false;
            for (ta.elems, 0..) |eid, i| if (eid != tb.elems[i]) break :blk false;
            break :blk true;
        },
        .Function => |fa| blk: {
            const fb = b.Function;
            if (fa.is_variadic != fb.is_variadic) break :blk false;
            if (fa.result != fb.result) break :blk false;
            if (fa.params.len != fb.params.len) break :blk false;
            for (fa.params, 0..) |pa, i| if (pa != fb.params[i]) break :blk false;
            break :blk true;
        },
        .Struct => |sa| blk: {
            const sb = b.Struct;
            if (sa.fields.len != sb.fields.len) break :blk false;
            for (sa.fields, 0..) |f, i| {
                if (!std.mem.eql(u8, f.name, sb.fields[i].name)) break :blk false;
                if (f.ty != sb.fields[i].ty) break :blk false;
            }
            break :blk true;
        },
    };
}

test "types: basic interning" {
    const gpa = std.heap.page_allocator;
    var arena = TypeArena.init(gpa);
    defer arena.deinit();

    const t_i32 = try arena.mk(.{ .I32 = {} });
    const t_i32b = try arena.mk(.{ .I32 = {} });
    try std.testing.expectEqual(t_i32, t_i32b);

    const ptr_i32 = try arena.mk(.{ .Ptr = .{ .elem = t_i32 } });
    const ptr_i32_2 = try arena.mk(.{ .Ptr = .{ .elem = t_i32 } });
    try std.testing.expectEqual(ptr_i32, ptr_i32_2);
}
