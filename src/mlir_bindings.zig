pub const c = @cImport({
    @cInclude("mlir-c/IR.h");
    @cInclude("mlir-c/Dialect/Func.h");
    @cInclude("mlir-c/RegisterEverything.h");
    @cInclude("mlir-c/ExecutionEngine.h");
    @cInclude("mlir-c/BuiltinAttributes.h");
    @cInclude("mlir-c/BuiltinTypes.h");
    @cInclude("mlir-c/Dialect/LLVM.h");
    @cInclude("mlir-c/Dialect/SCF.h");
    @cInclude("mlir-c/Diagnostics.h");
    @cInclude("mlir-c/Pass.h");
    @cInclude("mlir-c/Target/LLVMIR.h");
    @cInclude("llvm-c/Target.h");
    @cInclude("llvm-c/Transforms/PassBuilder.h");
    @cInclude("llvm-c/Core.h");
    @cInclude("llvm-c/IRReader.h");
    @cInclude("llvm-c/TargetMachine.h");
    @cInclude("llvm-c/BitWriter.h");
});

pub fn SmallVector(comptime T: type, comptime N: usize) type {
    return struct {
        inlineStorage: [N]T,
        heapStorage: ?[]T, // valid only when cap > N
        len: usize,
        cap: usize,
        alloc: std.mem.Allocator,

        const Self = @This();

        pub fn init(alloc: std.mem.Allocator) Self {
            return .{
                .inlineStorage = undefined,
                .heapStorage = null,
                .len = 0,
                .cap = N,
                .alloc = alloc,
            };
        }

        pub fn deinit(self: *Self) void {
            if (self.cap > N) {
                self.alloc.free(self.heapStorage.?);
            }
            self.heapStorage = null;
            self.len = 0;
            self.cap = 0;
        }

        // ---- views ----
        pub fn sliceConst(self: *const Self) []const T {
            return if (self.cap <= N)
                self.inlineStorage[0..self.len]
            else
                self.heapStorage.?[0..self.len];
        }
        pub fn slice(self: *Self) []T {
            return if (self.cap <= N)
                self.inlineStorage[0..self.len]
            else
                self.heapStorage.?[0..self.len];
        }

        pub fn size(self: *const Self) usize {
            return self.len;
        }
        pub fn capacity(self: *const Self) usize {
            return self.cap;
        }
        pub fn isEmpty(self: *const Self) bool {
            return self.len == 0;
        }

        pub fn atConst(self: *const Self, i: usize) T {
            std.debug.assert(i < self.len);
            return self.sliceConst()[i];
        }
        pub fn atRef(self: *Self, i: usize) *T {
            std.debug.assert(i < self.len);
            return &self.slice()[i];
        }

        pub fn clear(self: *Self) void {
            self.len = 0;
        }

        // Geometric growth: 2×, at least N, at least needed
        fn nextCap(self: *const Self, needed: usize) usize {
            var cap = if (self.cap < N) N else self.cap;
            if (cap < needed) {
                while (cap < needed) : (cap *= 2) {}
            }
            return cap;
        }

        fn bufConst(self: *const Self) []const T {
            return if (self.cap <= N) self.inlineStorage[0..self.cap] else self.heapStorage.?;
        }
        fn buf(self: *Self) []T {
            return if (self.cap <= N) self.inlineStorage[0..self.cap] else self.heapStorage.?;
        }

        pub fn push(self: *Self, value: T) void {
            if (self.len == self.cap) self.grow(self.nextCap(self.len + 1));
            self.buf()[self.len] = value; // write into capacity buffer
            self.len += 1;
        }

        pub fn pushSlice(self: *Self, src: []const T) void {
            if (src.len == 0) return;
            const need = self.len + src.len;
            if (need > self.cap) self.grow(self.nextCap(need));
            const b = self.buf();
            std.mem.copy(T, b[self.len..need], src);
            self.len = need;
        }

        pub fn popBack(self: *Self) T {
            std.debug.assert(self.len > 0);
            const b = if (self.cap <= N) self.inlineStorage[0..self.len] else self.heapStorage.?[0..self.len];
            const val = b[self.len - 1];
            self.len -= 1;
            return val;
        }

        pub fn reserve(self: *Self, newCap: usize) void {
            if (newCap > self.cap) self.grow(self.nextCap(newCap));
        }

        fn grow(self: *Self, newCap: usize) void {
            if (newCap <= N) {
                // switch to inline (rare; mainly defensive)
                if (self.cap > N) {
                    const old = self.heapStorage.?;
                    // copy back to inline
                    @memcpy(self.inlineStorage[0..self.len], old[0..self.len]);
                    self.alloc.free(old);
                    self.heapStorage = null;
                }
                self.cap = N;
                return;
            }

            // allocate new heap buffer
            var newBuf = self.alloc.alloc(T, newCap) catch @panic("SmallVector.grow: OOM");
            // copy from current storage
            if (self.cap <= N) {
                @memcpy(newBuf[0..self.len], self.inlineStorage[0..self.len]);
            } else {
                const old = self.heapStorage.?;
                @memcpy(newBuf[0..self.len], old[0..self.len]);
                self.alloc.free(old);
            }
            self.heapStorage = newBuf;
            self.cap = newCap;
        }

        // ----- optional: explicit ownership helpers -----

        /// Moves ownership into `dst` and leaves `self` empty.
        pub fn moveTo(self: *Self, dst: *Self) void {
            // Beware: shallow move of allocator; that’s what you had.
            dst.* = self.*;
            // poison self to avoid double free
            self.heapStorage = null;
            self.len = 0;
            self.cap = N;
        }

        /// Clones contents into a new vector (deep copy).
        pub fn clone(self: *const Self, alloc: std.mem.Allocator) Self {
            var out = Self.init(alloc);
            if (self.len > 0) {
                out.reserve(self.len);
                out.pushSlice(self.sliceConst());
            }
            return out;
        }
    };
}

const std = @import("std");

var global_alloc: std.mem.Allocator = undefined;

pub fn setGlobalAlloc(alloc: std.mem.Allocator) void {
    global_alloc = alloc;
}

pub const StringRef = struct {
    inner: c.MlirStringRef,

    pub fn from(s: []const u8) StringRef {
        return StringRef{
            .inner = c.MlirStringRef{
                .data = s.ptr,
                .length = s.len,
            },
        };
    }

    pub fn length(self: *StringRef) usize {
        return self.inner.length;
    }

    pub fn toSlice(self: *const StringRef) []const u8 {
        return self.inner.data[0..self.inner.length];
    }
};

pub const NamedAttribute = struct {
    inner: c.MlirNamedAttribute,
};

pub const LogicalResult = struct {
    inner: c.MlirLogicalResult,

    pub fn success(self: *LogicalResult) bool {
        return c.mlirLogicalResultIsSuccess(self.inner);
    }
    pub fn failure(self: *LogicalResult) bool {
        return !c.mlirLogicalResultIsSuccess(self.inner);
    }
};

pub const WalkResult = enum(c_int) {
    Advance = c.MlirWalkResultAdvance,
    Interrupt = c.MlirWalkResultInterrupt,
    Skip = c.MlirWalkResultSkip,
};

pub const WalkOrder = enum(c_int) {
    PreOrder = c.MlirWalkPreOrder,
    PostOrder = c.MlirWalkPostOrder,
};

//-------------------------------------
// Context
//-------------------------------------
pub const Context = struct {
    handle: c.MlirContext,

    pub fn create() Context {
        return Context{ .handle = c.mlirContextCreate() };
    }

    pub fn createWithThreading(threadingEnabled: bool) Context {
        return Context{ .handle = c.mlirContextCreateWithThreading(threadingEnabled) };
    }

    pub fn createWithRegistry(registry: DialectRegistry, threadingEnabled: bool) Context {
        return Context{
            .handle = c.mlirContextCreateWithRegistry(registry.handle, threadingEnabled),
        };
    }

    pub fn destroy(self: *Context) void {
        if (!self.isNull()) {
            c.mlirContextDestroy(self.handle);
            self.handle = undefined;
        }
    }

    pub fn isNull(self: *Context) bool {
        return c.mlirContextIsNull(self.handle);
    }

    pub fn equal(self: *Context, other: Context) bool {
        return c.mlirContextEqual(self.handle, other.handle);
    }

    pub fn setAllowUnregisteredDialects(self: *Context, allow: bool) void {
        c.mlirContextSetAllowUnregisteredDialects(self.handle, allow);
    }

    pub fn getAllowUnregisteredDialects(self: *Context) bool {
        return c.mlirContextGetAllowUnregisteredDialects(self.handle);
    }

    pub fn getNumRegisteredDialects(self: *Context) usize {
        return @intCast(c.mlirContextGetNumRegisteredDialects(self.handle));
    }

    pub fn appendDialectRegistry(self: *Context, registry: DialectRegistry) void {
        c.mlirContextAppendDialectRegistry(self.handle, registry.handle);
    }

    pub fn getNumLoadedDialects(self: *Context) usize {
        return @intCast(c.mlirContextGetNumLoadedDialects(self.handle));
    }

    pub fn getOrLoadDialect(self: *Context, name: StringRef) Dialect {
        return Dialect{
            .handle = c.mlirContextGetOrLoadDialect(self.handle, name.inner),
        };
    }

    pub fn enableMultithreading(self: *Context, enable: bool) void {
        c.mlirContextEnableMultithreading(self.handle, enable);
    }

    pub fn loadAllAvailableDialects(self: *Context) void {
        c.mlirContextLoadAllAvailableDialects(self.handle);
    }

    pub fn isRegisteredOperation(self: *Context, opName: StringRef) bool {
        return c.mlirContextIsRegisteredOperation(self.handle, opName.inner);
    }

    // If you have a thread pool:
    pub fn setThreadPool(self: *Context, threadPool: c.MlirLlvmThreadPool) void {
        c.mlirContextSetThreadPool(self.handle, threadPool);
    }
};

//-------------------------------------
// Dialect
//-------------------------------------
pub const Dialect = struct {
    handle: c.MlirDialect,

    pub fn isNull(self: *const Dialect) bool {
        return c.mlirDialectIsNull(self.handle);
    }

    pub fn getContext(self: *Dialect) Context {
        return Context{ .handle = c.mlirDialectGetContext(self.handle) };
    }

    pub fn equal(self: *Dialect, other: Dialect) bool {
        return c.mlirDialectEqual(self.handle, other.handle);
    }

    pub fn getNamespace(self: *Dialect) StringRef {
        return StringRef{ .inner = c.mlirDialectGetNamespace(self.handle) };
    }
};

//-------------------------------------
// DialectHandle
//-------------------------------------
pub const DialectHandle = struct {
    handle: c.MlirDialectHandle,

    pub fn getNamespace(self: *DialectHandle) StringRef {
        return StringRef{ .inner = c.mlirDialectHandleGetNamespace(self.handle) };
    }

    pub fn insertDialect(self: *DialectHandle, registry: DialectRegistry) void {
        c.mlirDialectHandleInsertDialect(self.handle, registry.handle);
    }

    pub fn registerDialect(self: *DialectHandle, ctx: Context) void {
        c.mlirDialectHandleRegisterDialect(self.handle, ctx.handle);
    }

    pub fn loadDialect(self: *DialectHandle, ctx: Context) Dialect {
        return Dialect{
            .handle = c.mlirDialectHandleLoadDialect(self.handle, ctx.handle),
        };
    }
};

//-------------------------------------
// DialectRegistry
//-------------------------------------
pub const DialectRegistry = struct {
    handle: c.MlirDialectRegistry,

    pub fn create() DialectRegistry {
        return DialectRegistry{ .handle = c.mlirDialectRegistryCreate() };
    }

    pub fn destroy(self: *DialectRegistry) void {
        if (!self.isNull()) {
            c.mlirDialectRegistryDestroy(self.handle);
            self.handle = undefined;
        }
    }

    pub fn isNull(self: *DialectRegistry) bool {
        return c.mlirDialectRegistryIsNull(self.handle);
    }
};

//-------------------------------------
// Location
//-------------------------------------
pub const Location = struct {
    handle: c.MlirLocation,

    pub fn isNull(self: *Location) bool {
        return c.mlirLocationIsNull(self.handle);
    }

    pub fn equal(self: *Location, other: Location) bool {
        return c.mlirLocationEqual(self.handle, other.handle);
    }

    pub fn getAttribute(self: *Location) Attribute {
        return Attribute{ .handle = c.mlirLocationGetAttribute(self.handle) };
    }

    pub fn fromAttribute(attr: Attribute) Location {
        return Location{ .handle = c.mlirLocationFromAttribute(attr.handle) };
    }

    pub fn fileLineColGet(ctx: Context, filename: StringRef, line: u32, col: u32) Location {
        return Location{
            .handle = c.mlirLocationFileLineColGet(ctx.handle, filename.inner, line, col),
        };
    }

    pub fn callSiteGet(callee: Location, caller: Location) Location {
        return Location{
            .handle = c.mlirLocationCallSiteGet(callee.handle, caller.handle),
        };
    }

    pub fn fusedGet(
        ctx: Context,
        locations: []const Location,
        metadata: Attribute,
    ) Location {
        var locs = SmallVector(c.MlirLocation, 8).init(global_alloc);
        for (locations) |loc| {
            locs.push(loc.handle);
        }
        return Location{ .handle = c.mlirLocationFusedGet(
            ctx.handle,
            @intCast(locs.len),
            @ptrCast(locs.slice()),
            metadata.handle,
        ) };
    }

    pub fn nameGet(ctx: Context, name: StringRef, childLoc: Location) Location {
        return Location{
            .handle = c.mlirLocationNameGet(ctx.handle, name.inner, childLoc.handle),
        };
    }

    pub fn unknownGet(ctx: Context) Location {
        return Location{ .handle = c.mlirLocationUnknownGet(ctx.handle) };
    }

    pub fn getContext(self: *Location) Context {
        return Context{ .handle = c.mlirLocationGetContext(self.handle) };
    }

    pub fn print(self: *Location, cb: fn ([]const u8, anyopaque) callconv(.c) void, userData: anyopaque) void {
        c.mlirLocationPrint(self.handle, cb, userData);
    }
};

//-------------------------------------
// Module
//-------------------------------------
pub const Module = struct {
    handle: c.MlirModule,

    pub fn createEmpty(loc: Location) Module {
        return Module{ .handle = c.mlirModuleCreateEmpty(loc.handle) };
    }

    pub fn createParse(ctx: Context, moduleStr: StringRef) Module {
        return Module{
            .handle = c.mlirModuleCreateParse(ctx.handle, moduleStr.inner),
        };
    }

    pub fn getContext(self: *Module) Context {
        return Context{ .handle = c.mlirModuleGetContext(self.handle) };
    }

    pub fn getBody(self: *const Module) Block {
        return Block{ .handle = c.mlirModuleGetBody(self.handle) };
    }

    pub fn isNull(self: *Module) bool {
        return c.mlirModuleIsNull(self.handle);
    }

    pub fn destroy(self: *Module) void {
        if (!self.isNull()) {
            c.mlirModuleDestroy(@field(self, "handle"));
            self.handle = undefined;
        }
    }

    pub fn getOperation(self: *const Module) Operation {
        return Operation{ .handle = c.mlirModuleGetOperation(self.handle) };
    }

    pub fn fromOperation(op: Operation) Module {
        return Module{ .handle = c.mlirModuleFromOperation(op.handle) };
    }
};

//-------------------------------------
// OperationState
//-------------------------------------
pub const OperationState = struct {
    // The underlying C struct
    state: c.MlirOperationState,

    /// Create a new operation state.
    pub fn get(name: StringRef, loc: Location) OperationState {
        return OperationState{ .state = c.mlirOperationStateGet(name.inner, loc.handle) };
    }

    pub fn addResults(self: *OperationState, results: []const Type) void {
        var tmp = SmallVector(c.MlirType, 8).init(global_alloc);
        for (results) |t| {
            tmp.push(t.handle);
        }
        c.mlirOperationStateAddResults(&self.state, @intCast(tmp.len), @ptrCast(tmp.slice()));
    }

    pub fn addOperands(self: *OperationState, operands: []const Value) void {
        var tmp = SmallVector(c.MlirValue, 8).init(global_alloc);
        for (operands) |v| {
            tmp.push(v.handle);
        }
        c.mlirOperationStateAddOperands(&self.state, @intCast(tmp.len), @ptrCast(tmp.slice()));
    }

    pub fn addOwnedRegions(self: *OperationState, regions: []const Region) void {
        var tmp = SmallVector(c.MlirRegion, 8).init(global_alloc);
        for (regions) |r| {
            tmp.push(r.handle);
        }
        c.mlirOperationStateAddOwnedRegions(&self.state, @intCast(tmp.len), @ptrCast(tmp.slice()));
    }

    pub fn addSuccessors(self: *OperationState, successors: []const Block) void {
        var tmp = SmallVector(c.MlirBlock, 8).init(global_alloc);
        for (successors) |b| {
            tmp.push(b.handle);
        }
        c.mlirOperationStateAddSuccessors(&self.state, @intCast(tmp.len), @ptrCast(tmp.slice()));
    }

    pub fn addAttributes(self: *OperationState, attrs: []const NamedAttribute) void {
        var tmp = SmallVector(c.MlirNamedAttribute, 8).init(global_alloc);
        for (attrs) |na| {
            tmp.push(na.inner);
        }
        c.mlirOperationStateAddAttributes(&self.state, @intCast(tmp.len), @ptrCast(tmp.slice()));
    }

    pub fn enableResultTypeInference(self: *OperationState) void {
        c.mlirOperationStateEnableResultTypeInference(&self.state);
    }
};

//-------------------------------------
// AsmState
//-------------------------------------
pub const AsmState = struct {
    handle: c.MlirAsmState,

    /// Create for an operation
    pub fn createForOperation(op: Operation, flags: OpPrintingFlags) AsmState {
        return AsmState{
            .handle = c.mlirAsmStateCreateForOperation(op.handle, flags.handle),
        };
    }

    /// Create for a value
    pub fn createForValue(value: Value, flags: OpPrintingFlags) AsmState {
        return AsmState{
            .handle = c.mlirAsmStateCreateForValue(value.handle, flags.handle),
        };
    }

    pub fn destroy(self: *AsmState) void {
        if (self.handle.ptr) |_| {
            c.mlirAsmStateDestroy(@field(self, "handle"));
            self.handle = undefined;
        }
    }
};

//-------------------------------------
// OpPrintingFlags
//-------------------------------------
pub const OpPrintingFlags = struct {
    handle: c.MlirOpPrintingFlags,

    pub fn create() OpPrintingFlags {
        return OpPrintingFlags{ .handle = c.mlirOpPrintingFlagsCreate() };
    }

    pub fn destroy(self: *OpPrintingFlags) void {
        if (self.handle.ptr) |_| {
            c.mlirOpPrintingFlagsDestroy(@field(self, "handle"));
            self.handle = undefined;
        }
    }

    pub fn elideLargeElementsAttrs(self: *OpPrintingFlags, largeElementLimit: usize) void {
        c.mlirOpPrintingFlagsElideLargeElementsAttrs(self.handle, @intCast(largeElementLimit));
    }

    pub fn elideLargeResourceString(self: *OpPrintingFlags, largeResourceLimit: usize) void {
        c.mlirOpPrintingFlagsElideLargeResourceString(self.handle, @intCast(largeResourceLimit));
    }

    pub fn enableDebugInfo(self: *OpPrintingFlags, enable: bool, prettyForm: bool) void {
        c.mlirOpPrintingFlagsEnableDebugInfo(self.handle, enable, prettyForm);
    }

    pub fn printGenericOpForm(self: *OpPrintingFlags) void {
        c.mlirOpPrintingFlagsPrintGenericOpForm(self.handle);
    }

    pub fn useLocalScope(self: *OpPrintingFlags) void {
        c.mlirOpPrintingFlagsUseLocalScope(self.handle);
    }

    pub fn assumeVerified(self: *OpPrintingFlags) void {
        c.mlirOpPrintingFlagsAssumeVerified(self.handle);
    }

    pub fn skipRegions(self: *OpPrintingFlags) void {
        c.mlirOpPrintingFlagsSkipRegions(self.handle);
    }
};

//-------------------------------------
// BytecodeWriterConfig
//-------------------------------------
pub const BytecodeWriterConfig = struct {
    handle: c.MlirBytecodeWriterConfig,

    pub fn create() BytecodeWriterConfig {
        return BytecodeWriterConfig{ .handle = c.mlirBytecodeWriterConfigCreate() };
    }

    pub fn destroy(self: *BytecodeWriterConfig) void {
        if (self.handle.ptr) |_| {
            c.mlirBytecodeWriterConfigDestroy(@field(self, "handle"));
            self.handle = undefined;
        }
    }

    pub fn desiredEmitVersion(self: *BytecodeWriterConfig, version: i64) void {
        c.mlirBytecodeWriterConfigDesiredEmitVersion(self.handle, version);
    }
};

//-------------------------------------
// Operation
//-------------------------------------
pub const Operation = struct {
    handle: c.MlirOperation,

    pub fn create(state: *OperationState) Operation {
        return Operation{ .handle = c.mlirOperationCreate(&state.state) };
    }

    pub fn createParse(ctx: Context, sourceStr: StringRef, sourceName: StringRef) Operation {
        return Operation{
            .handle = c.mlirOperationCreateParse(ctx.handle, sourceStr.inner, sourceName.inner),
        };
    }

    pub fn clone(op: Operation) Operation {
        return Operation{ .handle = c.mlirOperationClone(op.handle) };
    }

    pub fn destroy(self: *Operation) void {
        if (!self.isNull()) {
            c.mlirOperationDestroy(@field(self, "handle"));
            self.handle = undefined;
        }
    }

    pub fn removeFromParent(self: *Operation) void {
        c.mlirOperationRemoveFromParent(self.handle);
    }

    pub fn isNull(self: *const Operation) bool {
        return c.mlirOperationIsNull(self.handle);
    }

    pub fn equal(self: *Operation, other: *Operation) bool {
        return c.mlirOperationEqual(self.handle, other.handle);
    }

    pub fn getContext(self: *Operation) Context {
        return Context{ .handle = c.mlirOperationGetContext(self.handle) };
    }

    pub fn getLocation(self: *Operation) Location {
        return Location{ .handle = c.mlirOperationGetLocation(self.handle) };
    }

    pub fn getTypeID(self: *Operation) c.MlirTypeID {
        return c.mlirOperationGetTypeID(self.handle);
    }

    pub fn getName(self: *const Operation) Identifier {
        return Identifier{ .handle = c.mlirOperationGetName(self.handle) };
    }

    pub fn getBlock(self: *Operation) Block {
        return Block{ .handle = c.mlirOperationGetBlock(self.handle) };
    }

    pub fn getParentOperation(self: *Operation) Operation {
        return Operation{ .handle = c.mlirOperationGetParentOperation(self.handle) };
    }

    pub fn getNumRegions(self: *Operation) usize {
        return @intCast(c.mlirOperationGetNumRegions(self.handle));
    }

    pub fn getRegion(self: *const Operation, pos: usize) Region {
        return Region{
            .handle = c.mlirOperationGetRegion(self.handle, @intCast(pos)),
        };
    }

    pub fn getNextInBlock(self: *Operation) Operation {
        return Operation{ .handle = c.mlirOperationGetNextInBlock(self.handle) };
    }

    pub fn getNumOperands(self: *Operation) usize {
        return @intCast(c.mlirOperationGetNumOperands(self.handle));
    }

    pub fn getOperand(self: *const Operation, pos: usize) Value {
        return Value{ .handle = c.mlirOperationGetOperand(self.handle, @intCast(pos)) };
    }

    pub fn setOperand(self: *Operation, pos: usize, newValue: Value) void {
        c.mlirOperationSetOperand(self.handle, @intCast(pos), newValue.handle);
    }

    pub fn setOperands(self: *Operation, operands: []const Value) void {
        if (operands.len == 0) {
            c.mlirOperationSetOperands(self.handle, 0, null);
            return;
        }
        var tmp = SmallVector(c.MlirValue, 8).init(global_alloc);
        for (operands) |v| {
            tmp.push(v.handle);
        }
        c.mlirOperationSetOperands(self.handle, @intCast(tmp.len), @ptrCast(tmp.slice()));
    }

    pub fn getNumResults(self: *const Operation) usize {
        return @intCast(c.mlirOperationGetNumResults(self.handle));
    }

    pub fn getResult(self: *const Operation, pos: usize) Value {
        return Value{ .handle = c.mlirOperationGetResult(self.handle, @intCast(pos)) };
    }

    pub fn getNumSuccessors(self: *Operation) usize {
        return @intCast(c.mlirOperationGetNumSuccessors(self.handle));
    }

    pub fn getSuccessor(self: *Operation, pos: usize) Block {
        return Block{ .handle = c.mlirOperationGetSuccessor(self.handle, @intCast(pos)) };
    }

    pub fn setSuccessor(self: *Operation, pos: usize, block: Block) void {
        c.mlirOperationSetSuccessor(self.handle, @intCast(pos), block.handle);
    }

    pub fn hasInherentAttributeByName(self: *Operation, name: StringRef) bool {
        return c.mlirOperationHasInherentAttributeByName(self.handle, name.inner);
    }

    pub fn getInherentAttributeByName(self: *const Operation, name: StringRef) Attribute {
        return Attribute{
            .handle = c.mlirOperationGetInherentAttributeByName(self.handle, name.inner),
        };
    }

    pub fn setInherentAttributeByName(self: *Operation, name: StringRef, attr: Attribute) void {
        c.mlirOperationSetInherentAttributeByName(self.handle, name.inner, attr.handle);
    }

    pub fn getNumDiscardableAttributes(self: *Operation) usize {
        return @intCast(c.mlirOperationGetNumDiscardableAttributes(self.handle));
    }

    pub fn getDiscardableAttribute(self: *Operation, pos: usize) NamedAttribute {
        return NamedAttribute{
            .inner = c.mlirOperationGetDiscardableAttribute(self.handle, @intCast(pos)),
        };
    }

    pub fn getDiscardableAttributeByName(self: *Operation, name: StringRef) Attribute {
        return Attribute{
            .handle = c.mlirOperationGetDiscardableAttributeByName(self.handle, name.inner),
        };
    }

    pub fn setDiscardableAttributeByName(self: *Operation, name: StringRef, attr: Attribute) void {
        c.mlirOperationSetDiscardableAttributeByName(self.handle, name.inner, attr.handle);
    }

    pub fn removeDiscardableAttributeByName(self: *Operation, name: StringRef) bool {
        return c.mlirOperationRemoveDiscardableAttributeByName(self.handle, name.inner);
    }

    // (Deprecated) getAttributeByName, etc. omitted or rename if needed
    // ...

    pub fn print(self: *const Operation, callback: fn (c.MlirStringRef, ?*anyopaque) callconv(.c) void, userData: ?*anyopaque) void {
        c.mlirOperationPrint(self.handle, callback, userData);
    }

    pub fn printWithFlags(self: *Operation, flags: OpPrintingFlags, callback: fn ([]const u8, anyopaque) callconv(.c) void, userData: anyopaque) void {
        c.mlirOperationPrintWithFlags(self.handle, flags.handle, callback, userData);
    }

    pub fn printWithState(self: *Operation, state: AsmState, callback: fn ([]const u8, anyopaque) callconv(.c) void, userData: anyopaque) void {
        c.mlirOperationPrintWithState(self.handle, state.handle, callback, userData);
    }

    pub fn writeBytecode(self: *Operation, callback: fn ([]const u8, anyopaque) callconv(.c) void, userData: anyopaque) void {
        c.mlirOperationWriteBytecode(self.handle, callback, userData);
    }

    pub fn writeBytecodeWithConfig(self: *Operation, config: BytecodeWriterConfig, callback: fn ([]const u8, anyopaque) callconv(.c) void, userData: anyopaque) LogicalResult {
        return LogicalResult{
            .inner = c.mlirOperationWriteBytecodeWithConfig(self.handle, config.handle, callback, userData),
        };
    }

    pub fn dump(self: *const Operation) void {
        c.mlirOperationDump(self.handle);
    }

    pub fn verify(self: *const Operation) bool {
        return c.mlirOperationVerify(self.handle);
    }

    pub fn moveAfter(self: *Operation, other: Operation) void {
        c.mlirOperationMoveAfter(self.handle, other.handle);
    }

    pub fn moveBefore(self: *Operation, other: Operation) void {
        c.mlirOperationMoveBefore(self.handle, other.handle);
    }

    // pub fn walk(self: *Operation, callback: fn (Operation, *anyopaque) callconv(.c) WalkResult, userData: *anyopaque, walkOrder: WalkOrder) void {
    // c.mlirOperationWalk(
    //     self.handle,
    //     // bridging function pointer
    //     callconv(.c) function(op: c.MlirOperation, ud: *anyopaque) callconv(.c) c.MlirWalkResult {
    //         const wrapped = Operation{ .handle = op };
    //         const r = callback(wrapped, ud);
    //         switch (r) {
    //             WalkResult.Advance => return c.MlirWalkResultAdvance,
    //             WalkResult.Interrupt => return c.MlirWalkResultInterrupt,
    //             WalkResult.Skip => return c.MlirWalkResultSkip,
    //         }
    //     },
    //     userData,
    //     switch (walkOrder) {
    //         .PreOrder => c.MlirWalkPreOrder,
    //         .PostOrder => c.MlirWalkPostOrder,
    //     }
    // );
    // }
};

//-------------------------------------
// Region
//-------------------------------------
pub const Region = struct {
    handle: c.MlirRegion,

    pub fn create() Region {
        return Region{ .handle = c.mlirRegionCreate() };
    }

    pub fn destroy(self: *Region) void {
        if (!self.isNull()) {
            c.mlirRegionDestroy(@field(self, "handle"));
            self.handle = undefined;
        }
    }

    pub fn isNull(self: *Region) bool {
        return c.mlirRegionIsNull(self.handle);
    }

    pub fn equal(self: *Region, other: Region) bool {
        return c.mlirRegionEqual(self.handle, other.handle);
    }

    pub fn getFirstBlock(self: *const Region) Block {
        return Block{ .handle = c.mlirRegionGetFirstBlock(self.handle) };
    }

    pub fn appendOwnedBlock(self: *Region, block: Block) void {
        c.mlirRegionAppendOwnedBlock(self.handle, block.handle);
    }

    pub fn insertOwnedBlock(self: *Region, pos: usize, block: Block) void {
        c.mlirRegionInsertOwnedBlock(
            self.handle,
            @intCast(pos),
            block.handle,
        );
    }

    pub fn insertOwnedBlockAfter(self: *Region, reference: Block, block: Block) void {
        c.mlirRegionInsertOwnedBlockAfter(self.handle, reference.handle, block.handle);
    }

    pub fn insertOwnedBlockBefore(self: *Region, reference: Block, block: Block) void {
        c.mlirRegionInsertOwnedBlockBefore(self.handle, reference.handle, block.handle);
    }

    pub fn getNextInOperation(self: *Region) Region {
        return Region{ .handle = c.mlirRegionGetNextInOperation(self.handle) };
    }

    pub fn takeBody(self: *Region, source: Region) void {
        c.mlirRegionTakeBody(self.handle, source.handle);
    }
};

//-------------------------------------
// Block
//-------------------------------------
pub const Block = struct {
    handle: c.MlirBlock,

    pub fn create(argTypes: []const Type, argLocs: []const Location) Block {
        std.debug.assert(argTypes.len == argLocs.len);
        return Block{
            .handle = c.mlirBlockCreate(
                @intCast(argTypes.len),
                @ptrCast(argTypes),
                @ptrCast(argLocs),
            ),
        };
    }

    pub fn destroy(self: *Block) void {
        if (!self.isNull()) {
            c.mlirBlockDestroy(@field(self, "handle"));
            self.handle = undefined;
        }
    }

    pub fn detach(self: *Block) void {
        c.mlirBlockDetach(self.handle);
    }

    pub fn isNull(self: *Block) bool {
        return c.mlirBlockIsNull(self.handle);
    }

    pub fn equal(self: *Block, other: Block) bool {
        return c.mlirBlockEqual(self.handle, other.handle);
    }

    pub fn getParentOperation(self: *Block) Operation {
        return Operation{ .handle = c.mlirBlockGetParentOperation(self.handle) };
    }

    pub fn getParentRegion(self: *Block) Region {
        return Region{ .handle = c.mlirBlockGetParentRegion(self.handle) };
    }

    pub fn getNextInRegion(self: *Block) Block {
        return Block{ .handle = c.mlirBlockGetNextInRegion(self.handle) };
    }

    pub fn getFirstOperation(self: *const Block) Operation {
        return Operation{ .handle = c.mlirBlockGetFirstOperation(self.handle) };
    }

    pub fn getTerminator(self: *const Block) Operation {
        return Operation{ .handle = c.mlirBlockGetTerminator(self.handle) };
    }

    pub fn appendOwnedOperation(self: *Block, op: Operation) void {
        c.mlirBlockAppendOwnedOperation(self.handle, op.handle);
    }

    pub fn insertOwnedOperation(self: *Block, pos: usize, op: Operation) void {
        c.mlirBlockInsertOwnedOperation(self.handle, @intCast(pos), op.handle);
    }

    pub fn insertOwnedOperationAfter(self: *Block, reference: Operation, op: Operation) void {
        c.mlirBlockInsertOwnedOperationAfter(self.handle, reference.handle, op.handle);
    }

    pub fn insertOwnedOperationBefore(self: *Block, reference: Operation, op: Operation) void {
        c.mlirBlockInsertOwnedOperationBefore(self.handle, reference.handle, op.handle);
    }

    pub fn getNumArguments(self: *Block) usize {
        return @intCast(c.mlirBlockGetNumArguments(self.handle));
    }

    pub fn addArgument(self: *Block, ty: Type, loc: Location) Value {
        return Value{ .handle = c.mlirBlockAddArgument(self.handle, ty.handle, loc.handle) };
    }

    pub fn eraseArgument(self: *Block, index: u32) void {
        c.mlirBlockEraseArgument(self.handle, index);
    }

    pub fn insertArgument(self: *Block, pos: usize, ty: Type, loc: Location) Value {
        return Value{ .handle = c.mlirBlockInsertArgument(self.handle, @intCast(pos), ty.handle, loc.handle) };
    }

    pub fn getArgument(self: *const Block, pos: usize) Value {
        return Value{ .handle = c.mlirBlockGetArgument(self.handle, @intCast(pos)) };
    }

    pub fn print(self: *Block, callback: fn ([]const u8, anyopaque) callconv(.c) void, userData: anyopaque) void {
        c.mlirBlockPrint(self.handle, callback, userData);
    }
};

//-------------------------------------
// Value
//-------------------------------------
pub const Value = struct {
    handle: c.MlirValue,

    pub fn empty() Value {
        return Value{ .handle = c.MlirValue{} };
    }

    pub fn isNull(self: *Value) bool {
        return c.mlirValueIsNull(self.handle);
    }

    pub fn equal(self: *Value, other: Value) bool {
        return c.mlirValueEqual(self.handle, other.handle);
    }

    pub fn isABlockArgument(self: *Value) bool {
        return c.mlirValueIsABlockArgument(self.handle);
    }

    pub fn isAOpResult(self: *const Value) bool {
        return c.mlirValueIsAOpResult(self.handle);
    }

    pub fn blockArgumentGetOwner(self: *Value) Block {
        return Block{ .handle = c.mlirBlockArgumentGetOwner(self.handle) };
    }

    pub fn blockArgumentGetArgNumber(self: *Value) usize {
        return @intCast(c.mlirBlockArgumentGetArgNumber(self.handle));
    }

    pub fn blockArgumentSetType(self: *Value, ty: Type) void {
        c.mlirBlockArgumentSetType(self.handle, ty.handle);
    }

    pub fn opResultGetOwner(self: *const Value) Operation {
        return Operation{ .handle = c.mlirOpResultGetOwner(self.handle) };
    }

    pub fn opResultGetResultNumber(self: *Value) usize {
        return @intCast(c.mlirOpResultGetResultNumber(self.handle));
    }

    pub fn getType(self: *const Value) Type {
        return Type{ .handle = c.mlirValueGetType(self.handle) };
    }

    pub fn setType(self: *Value, ty: Type) void {
        c.mlirValueSetType(self.handle, ty.handle);
    }

    pub fn dump(self: *const Value) void {
        c.mlirValueDump(self.handle);
    }

    pub fn print(self: *const Value, cb: fn (c.MlirStringRef, ?*anyopaque) callconv(.c) void, userData: ?*anyopaque) void {
        c.mlirValuePrint(self.handle, cb, userData);
    }

    pub fn printAsOperand(self: *Value, state: AsmState, cb: fn ([]const u8, anyopaque) callconv(.c) void, userData: anyopaque) void {
        c.mlirValuePrintAsOperand(self.handle, state.handle, cb, userData);
    }

    pub fn getFirstUse(self: *Value) OpOperand {
        return OpOperand{ .handle = c.mlirValueGetFirstUse(self.handle) };
    }

    pub fn replaceAllUsesOfWith(of: Value, with: Value) void {
        c.mlirValueReplaceAllUsesOfWith(of.handle, with.handle);
    }
};

//-------------------------------------
// OpOperand
//-------------------------------------
pub const OpOperand = struct {
    handle: c.MlirOpOperand,

    pub fn isNull(self: *OpOperand) bool {
        return c.mlirOpOperandIsNull(self.handle);
    }

    pub fn getValue(self: *OpOperand) Value {
        return Value{ .handle = c.mlirOpOperandGetValue(self.handle) };
    }

    pub fn getOwner(self: *OpOperand) Operation {
        return Operation{ .handle = c.mlirOpOperandGetOwner(self.handle) };
    }

    pub fn getOperandNumber(self: *OpOperand) u32 {
        return c.mlirOpOperandGetOperandNumber(self.handle);
    }

    pub fn getNextUse(self: *OpOperand) OpOperand {
        return OpOperand{ .handle = c.mlirOpOperandGetNextUse(self.handle) };
    }
};

//-------------------------------------
// Identifier
//-------------------------------------
pub const Identifier = struct {
    handle: c.MlirIdentifier,

    pub fn get(ctx: Context, strref: StringRef) Identifier {
        return Identifier{
            .handle = c.mlirIdentifierGet(ctx.handle, strref.inner),
        };
    }

    pub fn getContext(self: *Identifier) Context {
        return Context{ .handle = c.mlirIdentifierGetContext(self.handle) };
    }

    pub fn equal(self: *Identifier, other: Identifier) bool {
        return c.mlirIdentifierEqual(self.handle, other.handle);
    }

    pub fn str(self: *const Identifier) StringRef {
        return StringRef{ .inner = c.mlirIdentifierStr(self.handle) };
    }
};

//-------------------------------------
// SymbolTable
//-------------------------------------
pub const SymbolTable = struct {
    handle: c.MlirSymbolTable,

    pub fn create(op: Operation) SymbolTable {
        return SymbolTable{ .handle = c.mlirSymbolTableCreate(op.handle) };
    }

    pub fn isNull(self: *SymbolTable) bool {
        return c.mlirSymbolTableIsNull(self.handle);
    }

    pub fn destroy(self: *SymbolTable) void {
        if (!self.isNull()) {
            c.mlirSymbolTableDestroy(@field(self, "handle"));
            self.handle = undefined;
        }
    }

    pub fn lookup(self: *SymbolTable, name: StringRef) Operation {
        return Operation{
            .handle = c.mlirSymbolTableLookup(self.handle, name.inner),
        };
    }

    pub fn insert(self: *SymbolTable, op: Operation) Attribute {
        return Attribute{
            .handle = c.mlirSymbolTableInsert(self.handle, op.handle),
        };
    }

    pub fn erase(self: *SymbolTable, op: Operation) void {
        c.mlirSymbolTableErase(self.handle, op.handle);
    }

    pub fn replaceAllSymbolUses(oldSymbol: StringRef, newSymbol: StringRef, from: Operation) LogicalResult {
        return LogicalResult{ .inner = c.mlirSymbolTableReplaceAllSymbolUses(
            oldSymbol.inner,
            newSymbol.inner,
            from.handle,
        ) };
    }

    // pub fn walkSymbolTables(from: Operation, allSymUsesVisible: bool, callback: fn (Operation, bool, *anyopaque) callconv(.c) void, userData: *anyopaque) void {
    // c.mlirSymbolTableWalkSymbolTables(
    //     from.handle,
    //     allSymUsesVisible,
    //     callconv(.c) function(op: c.MlirOperation, visible: bool, ud: *anyopaque) callconv(.c) void {
    //         const wrapped = Operation{ .handle = op };
    //         callback(wrapped, visible, ud);
    //     },
    //     userData
    // );
    // }

    pub fn getSymbolAttributeName() StringRef {
        return StringRef{ .inner = c.mlirSymbolTableGetSymbolAttributeName() };
    }

    pub fn getVisibilityAttributeName() StringRef {
        return StringRef{ .inner = c.mlirSymbolTableGetVisibilityAttributeName() };
    }
};

/// Appends all upstream dialects and extensions to the dialect registry.
pub fn registerAllDialects(registry: DialectRegistry) void {
    c.mlirRegisterAllDialects(registry.handle);
}

/// Register all translations to LLVM IR for dialects that can support it.
pub fn registerAllLLVMTranslations(ctx: Context) void {
    c.mlirRegisterAllLLVMTranslations(ctx.handle);
}

/// Register all compiler passes of MLIR.
pub fn registerAllPasses() void {
    c.mlirRegisterAllPasses();
}

pub const ExecutionEngine = struct {
    handle: c.MlirExecutionEngine,

    /// Create an ExecutionEngine from a Module.
    /// - module: The Module to JIT.
    /// - optLevel: Optimization level (0, 1, 2, 3).
    /// - sharedLibPaths: List of dynamic libraries to load.
    /// - enableObjectDump: Dump compiled code to object file for debugging.
    pub fn create(module: Module, optLevel: i32, sharedLibPaths: []StringRef, enableObjectDump: bool) ExecutionEngine {
        // Prepare the C array of MLIR string refs for sharedLibPaths.
        if (sharedLibPaths.len == 0) {
            return ExecutionEngine{
                .handle = c.mlirExecutionEngineCreate(module.handle, optLevel, 0, null, enableObjectDump),
            };
        } else {
            var tmpPaths = SmallVector(c.MlirStringRef, 8).init(global_alloc);
            for (sharedLibPaths) |sr| {
                tmpPaths.push(sr.inner);
            }

            return ExecutionEngine{
                .handle = c.mlirExecutionEngineCreate(module.handle, optLevel, @intCast(sharedLibPaths.len), @ptrCast(tmpPaths.slice()), enableObjectDump),
            };
        }
    }

    /// Destroy the ExecutionEngine instance.
    pub fn destroy(self: *ExecutionEngine) void {
        if (!self.isNull()) {
            c.mlirExecutionEngineDestroy(self.handle);
            self.handle = undefined;
        }
    }

    /// Check if this ExecutionEngine is null.
    pub fn isNull(self: *ExecutionEngine) bool {
        return c.mlirExecutionEngineIsNull(self.handle);
    }

    // /// Invoke a function by name, passing arguments as an array of pointers.
    // /// - functionName: Name of the function (must have `llvm.emit_c_interface`).
    // /// - arguments: The raw pointer array to pass into the function.
    // /// Returns a LogicalResult indicating success/failure.
    // pub fn invokePacked(
    //     self: ExecutionEngine,
    //     functionName: StringRef,
    //     arguments: [][]align(@alignOf(anyopaque) u8) // or whatever type is best
    // ) LogicalResult {
    //     // Typically you'd pass them as `[]*anyopaque`.
    //     // We'll do a pointer cast to `void**`.
    //     var ptr = if (arguments.len == 0) null else @ptrCast(*c_void, arguments.ptr);
    //     return LogicalResult{
    //         .inner = c.mlirExecutionEngineInvokePacked(
    //             self.handle,
    //             functionName.inner,
    //             @ptrCast([*c]*c_void, ptr),
    //         ),
    //     };
    // }

    /// Look up the "packed" version of a native function by name. Returns `?*anyopaque`.
    /// This is the wrapper that expects an `llvm.emit_c_interface`.
    pub fn lookupPacked(self: ExecutionEngine, functionName: StringRef) ?*anyopaque {
        const sym = c.mlirExecutionEngineLookupPacked(self.handle, functionName.inner);
        return if (sym == null) null else @ptrCast(sym);
    }

    /// Look up a native function by name. Returns `?*anyopaque`.
    pub fn lookup(self: ExecutionEngine, functionName: StringRef) ?*anyopaque {
        const sym = c.mlirExecutionEngineLookup(self.handle, functionName.inner);
        return if (sym == null) null else @ptrCast(sym);
    }

    /// Register a symbol (by name) so that JITed code can resolve it.
    pub fn registerSymbol(self: ExecutionEngine, name: StringRef, sym: *anyopaque) void {
        c.mlirExecutionEngineRegisterSymbol(self.handle, name.inner, sym);
    }

    /// Dump as object file.
    pub fn dumpToObjectFile(self: ExecutionEngine, filename: StringRef) void {
        c.mlirExecutionEngineDumpToObjectFile(self.handle, filename.inner);
    }
};

// =============================
// Attribute Wrapper
// =============================

pub const Attribute = struct {
    handle: c.MlirAttribute,

    pub fn empty() Attribute {
        return Attribute{ .handle = c.MlirAttribute{} };
    }

    pub fn parseGet(ctx: Context, attrStr: StringRef) Attribute {
        return Attribute{ .handle = c.mlirAttributeParseGet(ctx.handle, attrStr.inner) };
    }

    pub fn getContext(self: *Attribute) Context {
        return Context{ .handle = c.mlirAttributeGetContext(self.handle) };
    }

    pub fn getType(self: *Attribute) Type {
        return Type{ .handle = c.mlirAttributeGetType(self.handle) };
    }

    pub fn getTypeID(self: *Attribute) c.MlirTypeID {
        return c.mlirAttributeGetTypeID(self.handle);
    }

    pub fn getDialect(self: *Attribute) Dialect {
        return Dialect{ .handle = c.mlirAttributeGetDialect(self.handle) };
    }

    pub fn isNull(self: *const Attribute) bool {
        return c.mlirAttributeIsNull(self.handle);
    }

    pub fn equal(self: *const Attribute, other: *const Attribute) bool {
        return c.mlirAttributeEqual(self.handle, other.handle);
    }

    pub fn print(self: *const Attribute, cb: fn (c.MlirStringRef, ?*anyopaque) callconv(.c) void, userData: ?*anyopaque) void {
        c.mlirAttributePrint(self.handle, cb, userData);
    }

    pub fn dump(self: *const Attribute) void {
        c.mlirAttributeDump(self.handle);
    }

    pub fn namedAttributeGet(self: *Attribute, name: Identifier) NamedAttribute {
        return NamedAttribute{ .inner = c.mlirNamedAttributeGet(name.handle, self.handle) };
    }
    /// Returns an empty (null) attribute.
    pub fn getNull() Attribute {
        return Attribute{ .handle = c.mlirAttributeGetNull() };
    }

    /// Checks whether the attribute is a Location attribute.
    pub fn isALocation(self: Attribute) bool {
        return c.mlirAttributeIsALocation(self.handle);
    }

    /// Checks whether the attribute is an AffineMap attribute.
    pub fn isAAffineMap(self: Attribute) bool {
        return c.mlirAttributeIsAAffineMap(self.handle);
    }

    /// Creates an AffineMap attribute from an AffineMap.
    pub fn affineMapAttrGet(map: AffineMap) Attribute {
        return Attribute{ .handle = c.mlirAffineMapAttrGet(map.handle) };
    }

    /// Retrieves the AffineMap from an AffineMap attribute.
    pub fn affineMapAttrGetValue(self: Attribute) AffineMap {
        return AffineMap{ .handle = c.mlirAffineMapAttrGetValue(self.handle) };
    }

    /// Retrieves the TypeID of an AffineMap attribute.
    pub fn affineMapAttrGetTypeID() c.MlirTypeID {
        return c.mlirAffineMapAttrGetTypeID();
    }

    /// Checks whether the attribute is an Array attribute.
    pub fn isAArray(self: Attribute) bool {
        return c.mlirAttributeIsAArray(self.handle);
    }

    /// Creates an Array attribute from a list of Attributes.
    pub fn arrayAttrGet(ctx: Context, elements: []const Attribute) Attribute {
        if (elements.len == 0) {
            return Attribute{ .handle = c.mlirArrayAttrGet(ctx.handle, 0, null) };
        } else {
            var tmp = SmallVector(c.MlirAttribute, 8).init(global_alloc);
            for (elements) |e| {
                tmp.push(e.handle);
            }
            return Attribute{
                .handle = c.mlirArrayAttrGet(ctx.handle, @intCast(elements.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Retrieves the number of elements in an Array attribute.
    pub fn arrayAttrGetNumElements(self: Attribute) usize {
        return @intCast(c.mlirArrayAttrGetNumElements(self.handle));
    }

    /// Retrieves the element at the specified position in an Array attribute.
    pub fn arrayAttrGetElement(self: Attribute, pos: usize) Attribute {
        return Attribute{ .handle = c.mlirArrayAttrGetElement(self.handle, @intCast(pos)) };
    }

    /// Retrieves the TypeID of an Array attribute.
    pub fn arrayAttrGetTypeID() c.MlirTypeID {
        return c.mlirArrayAttrGetTypeID();
    }

    /// Checks whether the attribute is a Dictionary attribute.
    pub fn isADictionary(self: Attribute) bool {
        return c.mlirAttributeIsADictionary(self.handle);
    }

    /// Creates a Dictionary attribute from a list of NamedAttributes.
    pub fn dictionaryAttrGet(ctx: Context, elements: []const NamedAttribute) Attribute {
        if (elements.len == 0) {
            return Attribute{ .handle = c.mlirDictionaryAttrGet(ctx.handle, 0, null) };
        } else {
            var tmp = SmallVector(c.MlirNamedAttribute, 8).init(global_alloc);
            for (elements) |na| {
                tmp.push(na.inner);
            }
            return Attribute{
                .handle = c.mlirDictionaryAttrGet(ctx.handle, @intCast(elements.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Retrieves the number of elements in a Dictionary attribute.
    pub fn dictionaryAttrGetNumElements(self: Attribute) usize {
        return @intCast(c.mlirDictionaryAttrGetNumElements(self.handle));
    }

    /// Retrieves the NamedAttribute at the specified position in a Dictionary attribute.
    pub fn dictionaryAttrGetElement(self: Attribute, pos: usize) NamedAttribute {
        return NamedAttribute{ .inner = c.mlirDictionaryAttrGetElement(self.handle, @intCast(pos)) };
    }

    /// Retrieves the element by name in a Dictionary attribute.
    /// Returns a null Attribute if the name does not exist.
    pub fn dictionaryAttrGetElementByName(self: Attribute, name: StringRef) Attribute {
        return Attribute{ .handle = c.mlirDictionaryAttrGetElementByName(self.handle, name.inner) };
    }

    /// Retrieves the TypeID of a Dictionary attribute.
    pub fn dictionaryAttrGetTypeID() c.MlirTypeID {
        return c.mlirDictionaryAttrGetTypeID();
    }

    /// Checks whether the attribute is a Float attribute.
    pub fn isAFloat(self: Attribute) bool {
        return c.mlirAttributeIsAFloat(self.handle);
    }

    /// Creates a Float attribute with a double value.
    pub fn floatAttrDoubleGet(ctx: Context, ty: Type, value: f64) Attribute {
        return Attribute{ .handle = c.mlirFloatAttrDoubleGet(ctx.handle, ty.handle, value) };
    }

    /// Creates a Float attribute with a double value, checking type validity.
    /// Returns a null Attribute if the type is invalid.
    pub fn floatAttrDoubleGetChecked(loc: c.MlirLocation, ty: Type, value: f64) Attribute {
        return Attribute{ .handle = c.mlirFloatAttrDoubleGetChecked(loc, ty.handle, value) };
    }

    /// Retrieves the double value from a Float attribute.
    pub fn floatAttrGetValueDouble(self: Attribute) f64 {
        return c.mlirFloatAttrGetValueDouble(self.handle);
    }

    /// Retrieves the TypeID of a Float attribute.
    pub fn floatAttrGetTypeID() c.MlirTypeID {
        return c.mlirFloatAttrGetTypeID();
    }

    /// Checks whether the attribute is an Integer attribute.
    pub fn isAInteger(self: Attribute) bool {
        return c.mlirAttributeIsAInteger(self.handle);
    }

    /// Creates an Integer attribute with a 64-bit signed value.
    pub fn integerAttrGet(ty: Type, value: i64) Attribute {
        return Attribute{ .handle = c.mlirIntegerAttrGet(ty.handle, value) };
    }

    /// Retrieves the signed integer value from an Integer attribute.
    pub fn integerAttrGetValueInt(self: Attribute) i64 {
        return c.mlirIntegerAttrGetValueInt(self.handle);
    }

    /// Retrieves the signed integer value from an Integer attribute.
    pub fn integerAttrGetValueSInt(self: Attribute) i64 {
        return c.mlirIntegerAttrGetValueSInt(self.handle);
    }

    /// Retrieves the unsigned integer value from an Integer attribute.
    pub fn integerAttrGetValueUInt(self: Attribute) u64 {
        return c.mlirIntegerAttrGetValueUInt(self.handle);
    }

    /// Retrieves the TypeID of an Integer attribute.
    pub fn integerAttrGetTypeID() c.MlirTypeID {
        return c.mlirIntegerAttrGetTypeID();
    }

    /// Checks whether the attribute is a Bool attribute.
    pub fn isABool(self: Attribute) bool {
        return c.mlirAttributeIsABool(self.handle);
    }

    /// Creates a Bool attribute with the given value.
    pub fn boolAttrGet(ctx: Context, value: bool) Attribute {
        return Attribute{ .handle = c.mlirBoolAttrGet(ctx.handle, if (value) 1 else 0) };
    }

    /// Retrieves the boolean value from a Bool attribute.
    pub fn boolAttrGetValue(self: Attribute) bool {
        return c.mlirBoolAttrGetValue(self.handle);
    }

    /// Checks whether the attribute is an IntegerSet attribute.
    pub fn isAIntegerSet(self: Attribute) bool {
        return c.mlirAttributeIsAIntegerSet(self.handle);
    }

    /// Creates an IntegerSet attribute from an IntegerSet.
    pub fn integerSetAttrGet(set: IntegerSet) Attribute {
        return Attribute{ .handle = c.mlirIntegerSetAttrGet(set.handle) };
    }

    /// Retrieves the IntegerSet from an IntegerSet attribute.
    pub fn integerSetAttrGetValue(self: Attribute) IntegerSet {
        return IntegerSet{ .handle = c.mlirIntegerSetAttrGetValue(self.handle) };
    }

    /// Retrieves the TypeID of an IntegerSet attribute.
    pub fn integerSetAttrGetTypeID() c.MlirTypeID {
        return c.mlirIntegerSetAttrGetTypeID();
    }

    /// Checks whether the attribute is an Opaque attribute.
    pub fn isAOpaque(self: Attribute) bool {
        return c.mlirAttributeIsAOpaque(self.handle);
    }

    /// Creates an Opaque attribute with the given data.
    pub fn opaqueAttrGet(ctx: Context, dialectNamespace: StringRef, data: []const u8, ty: Type) Attribute {
        if (data.len == 0) {
            return Attribute{
                .handle = c.mlirOpaqueAttrGet(ctx.handle, dialectNamespace.inner, 0, null, ty.handle),
            };
        } else {
            return Attribute{
                .handle = c.mlirOpaqueAttrGet(ctx.handle, dialectNamespace.inner, @intCast(data.len), @ptrCast(data.ptr), ty.handle),
            };
        }
    }

    /// Retrieves the dialect namespace from an Opaque attribute.
    pub fn opaqueAttrGetDialectNamespace(self: Attribute) StringRef {
        return StringRef{ .inner = c.mlirOpaqueAttrGetDialectNamespace(self.handle) };
    }

    /// Retrieves the raw data from an Opaque attribute.
    pub fn opaqueAttrGetData(self: Attribute) StringRef {
        return StringRef{ .inner = c.mlirOpaqueAttrGetData(self.handle) };
    }

    /// Retrieves the TypeID of an Opaque attribute.
    pub fn opaqueAttrGetTypeID() c.MlirTypeID {
        return c.mlirOpaqueAttrGetTypeID();
    }

    /// Checks whether the attribute is a String attribute.
    pub fn isAString(self: Attribute) bool {
        return c.mlirAttributeIsAString(self.handle);
    }

    /// Creates a String attribute with the given string.
    pub fn stringAttrGet(ctx: Context, s: StringRef) Attribute {
        return Attribute{ .handle = c.mlirStringAttrGet(ctx.handle, s.inner) };
    }

    /// Creates a typed String attribute with the given string and type.
    pub fn stringAttrTypedGet(ty: Type, s: StringRef) Attribute {
        return Attribute{ .handle = c.mlirStringAttrTypedGet(ty.handle, s.inner) };
    }

    /// Retrieves the string value from a String attribute.
    pub fn stringAttrGetValue(self: Attribute) StringRef {
        return StringRef{ .inner = c.mlirStringAttrGetValue(self.handle) };
    }

    /// Retrieves the TypeID of a String attribute.
    pub fn stringAttrGetTypeID() c.MlirTypeID {
        return c.mlirStringAttrGetTypeID();
    }

    /// Checks whether the attribute is a SymbolRef attribute.
    pub fn isASymbolRef(self: Attribute) bool {
        return c.mlirAttributeIsASymbolRef(self.handle);
    }

    /// Creates a SymbolRef attribute with the given symbol and nested references.
    pub fn symbolRefAttrGet(ctx: Context, symbol: StringRef, references: []const Attribute) Attribute {
        if (references.len == 0) {
            return Attribute{ .handle = c.mlirSymbolRefAttrGet(ctx.handle, symbol.inner, 0, null) };
        } else {
            var tmp = SmallVector(c.MlirAttribute, 8).init(global_alloc);
            for (references) |r| {
                tmp.push(r.handle);
            }
            return Attribute{
                .handle = c.mlirSymbolRefAttrGet(ctx.handle, symbol.inner, @intCast(references.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Retrieves the root reference symbol from a SymbolRef attribute.
    pub fn symbolRefAttrGetRootReference(self: Attribute) StringRef {
        return StringRef{ .inner = c.mlirSymbolRefAttrGetRootReference(self.handle) };
    }

    /// Retrieves the leaf reference symbol from a SymbolRef attribute.
    pub fn symbolRefAttrGetLeafReference(self: Attribute) StringRef {
        return StringRef{ .inner = c.mlirSymbolRefAttrGetLeafReference(self.handle) };
    }

    /// Retrieves the number of nested references in a SymbolRef attribute.
    pub fn symbolRefAttrGetNumNestedReferences(self: Attribute) usize {
        return @intCast(c.mlirSymbolRefAttrGetNumNestedReferences(self.handle));
    }

    /// Retrieves the nested reference at the specified position in a SymbolRef attribute.
    pub fn symbolRefAttrGetNestedReference(self: Attribute, pos: usize) Attribute {
        return Attribute{ .handle = c.mlirSymbolRefAttrGetNestedReference(self.handle, @intCast(pos)) };
    }

    /// Retrieves the TypeID of a SymbolRef attribute.
    pub fn symbolRefAttrGetTypeID() c.MlirTypeID {
        return c.mlirSymbolRefAttrGetTypeID();
    }

    /// Creates a Distinct attribute referencing another attribute.
    pub fn distinctAttrCreate(referenced: Attribute) Attribute {
        return Attribute{ .handle = c.mlirDisctinctAttrCreate(referenced.handle) };
    }

    /// Checks whether the attribute is a FlatSymbolRef attribute.
    pub fn isAFlatSymbolRef(self: Attribute) bool {
        return c.mlirAttributeIsAFlatSymbolRef(self.handle);
    }

    /// Creates a FlatSymbolRef attribute with the given symbol.
    pub fn flatSymbolRefAttrGet(ctx: Context, symbol: StringRef) Attribute {
        return Attribute{ .handle = c.mlirFlatSymbolRefAttrGet(ctx.handle, symbol.inner) };
    }

    /// Retrieves the symbol string from a FlatSymbolRef attribute.
    pub fn flatSymbolRefAttrGetValue(self: Attribute) StringRef {
        return StringRef{ .inner = c.mlirFlatSymbolRefAttrGetValue(self.handle) };
    }

    /// Checks whether the attribute is a Type attribute.
    pub fn isAType(self: Attribute) bool {
        return c.mlirAttributeIsAType(self.handle);
    }

    /// Creates a Type attribute wrapping a given Type.
    pub fn typeAttrGet(ty: Type) Attribute {
        return Attribute{ .handle = c.mlirTypeAttrGet(ty.handle) };
    }

    /// Retrieves the Type from a Type attribute.
    pub fn typeAttrGetValue(self: Attribute) Type {
        return Type{ .handle = c.mlirTypeAttrGetValue(self.handle) };
    }

    /// Retrieves the TypeID of a Type attribute.
    pub fn typeAttrGetTypeID() c.MlirTypeID {
        return c.mlirTypeAttrGetTypeID();
    }

    /// Checks whether the attribute is a Unit attribute.
    pub fn isAUnit(self: Attribute) bool {
        return c.mlirAttributeIsAUnit(self.handle);
    }

    /// Creates a Unit attribute.
    pub fn unitAttrGet(ctx: Context) Attribute {
        return Attribute{ .handle = c.mlirUnitAttrGet(ctx.handle) };
    }

    /// Retrieves the TypeID of a Unit attribute.
    pub fn unitAttrGetTypeID() c.MlirTypeID {
        return c.mlirUnitAttrGetTypeID();
    }

    /// Checks whether the attribute is an Elements attribute.
    pub fn isAElements(self: Attribute) bool {
        return c.mlirAttributeIsAElements(self.handle);
    }

    /// Retrieves the value at a rank-dimensional index from an Elements attribute.
    /// `idxs` should be a slice of unsigned 64-bit integers representing the index in each dimension.
    pub fn elementsAttrGetValue(self: Attribute, idxs: []const u64) Attribute {
        const rank: isize = @intCast(idxs.len);
        return Attribute{ .handle = c.mlirElementsAttrGetValue(self.handle, rank, idxs.ptr) };
    }

    /// Checks whether the given rank-dimensional index is valid in the Elements attribute.
    pub fn elementsAttrIsValidIndex(self: Attribute, idxs: []const u64) bool {
        const rank: isize = @intCast(idxs.len);
        return c.mlirElementsAttrIsValidIndex(self.handle, rank, idxs.ptr);
    }

    /// Retrieves the total number of elements in an Elements attribute.
    pub fn elementsAttrGetNumElements(self: Attribute) i64 {
        return c.mlirElementsAttrGetNumElements(self.handle);
    }

    /// Checks whether the attribute is a DenseArray attribute.
    pub fn isADenseBoolArray(self: Attribute) bool {
        return c.mlirAttributeIsADenseBoolArray(self.handle);
    }
    pub fn isADenseI8Array(self: Attribute) bool {
        return c.mlirAttributeIsADenseI8Array(self.handle);
    }
    pub fn isADenseI16Array(self: Attribute) bool {
        return c.mlirAttributeIsADenseI16Array(self.handle);
    }
    pub fn isADenseI32Array(self: Attribute) bool {
        return c.mlirAttributeIsADenseI32Array(self.handle);
    }
    pub fn isADenseI64Array(self: Attribute) bool {
        return c.mlirAttributeIsADenseI64Array(self.handle);
    }
    pub fn isADenseF32Array(self: Attribute) bool {
        return c.mlirAttributeIsADenseF32Array(self.handle);
    }
    pub fn isADenseF64Array(self: Attribute) bool {
        return c.mlirAttributeIsADenseF64Array(self.handle);
    }

    /// Creates a DenseBoolArray attribute.
    pub fn denseBoolArrayGet(ctx: Context, vals: []const bool) Attribute {
        if (vals.len == 0) {
            return Attribute{ .handle = c.mlirDenseBoolArrayGet(ctx.handle, 0, null) };
        } else {
            var tmp = SmallVector(c.int, 8).init(global_alloc);
            for (vals) |v| {
                tmp.push(if (v) 1 else 0);
            }

            return Attribute{
                .handle = c.mlirDenseBoolArrayGet(ctx.handle, @intCast(vals.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Creates a DenseI8Array attribute.
    pub fn denseI8ArrayGet(ctx: Context, vals: []const i8) Attribute {
        if (vals.len == 0) {
            return Attribute{ .handle = c.mlirDenseI8ArrayGet(ctx.handle, 0, null) };
        } else {
            var tmp = SmallVector(i8, 8).init(global_alloc);
            for (vals) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirDenseI8ArrayGet(ctx.handle, @intCast(vals.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Creates a DenseI16Array attribute.
    pub fn denseI16ArrayGet(ctx: Context, vals: []const i16) Attribute {
        if (vals.len == 0) {
            return Attribute{ .handle = c.mlirDenseI16ArrayGet(ctx.handle, 0, null) };
        } else {
            var tmp = SmallVector(i16, 8).init(global_alloc);
            for (vals) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirDenseI16ArrayGet(ctx.handle, @intCast(vals.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Creates a DenseI32Array attribute.
    pub fn denseI32ArrayGet(ctx: Context, vals: []const i32) Attribute {
        if (vals.len == 0) {
            return Attribute{ .handle = c.mlirDenseI32ArrayGet(ctx.handle, 0, null) };
        } else {
            return Attribute{
                .handle = c.mlirDenseI32ArrayGet(ctx.handle, @intCast(vals.len), @ptrCast(vals)),
            };
        }
    }

    /// Creates a DenseI64Array attribute.
    pub fn denseI64ArrayGet(ctx: Context, vals: []const i64) Attribute {
        if (vals.len == 0) {
            return Attribute{ .handle = c.mlirDenseI64ArrayGet(ctx.handle, 0, null) };
        } else {
            var tmp = SmallVector(i64, 8).init(global_alloc);
            for (vals) |v| {
                tmp.push(v);
            }

            return Attribute{
                .handle = c.mlirDenseI64ArrayGet(ctx.handle, @intCast(vals.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Creates a DenseF32Array attribute.
    pub fn denseF32ArrayGet(ctx: Context, vals: []const f32) Attribute {
        if (vals.len == 0) {
            return Attribute{ .handle = c.mlirDenseF32ArrayGet(ctx.handle, 0, null) };
        } else {
            var tmp = SmallVector(f32, 8).init(global_alloc);
            for (vals) |v| {
                tmp.push(v);
            }

            return Attribute{
                .handle = c.mlirDenseF32ArrayGet(ctx.handle, @intCast(vals.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Creates a DenseF64Array attribute.
    pub fn denseF64ArrayGet(ctx: Context, vals: []const f64) Attribute {
        if (vals.len == 0) {
            return Attribute{ .handle = c.mlirDenseF64ArrayGet(ctx.handle, 0, null) };
        } else {
            var tmp = SmallVector(f64, 8).init(global_alloc);
            for (vals) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirDenseF64ArrayGet(ctx.handle, @intCast(vals.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Retrieves the number of elements in a DenseArray attribute.
    pub fn denseArrayGetNumElements(self: Attribute) usize {
        return @intCast(c.mlirDenseArrayGetNumElements(self.handle));
    }

    /// Retrieves a boolean element from a DenseBoolArray attribute.
    pub fn denseBoolArrayGetElement(self: Attribute, pos: usize) bool {
        return c.mlirDenseBoolArrayGetElement(self.handle, @intCast(pos)) != 0;
    }

    /// Retrieves an i8 element from a DenseI8Array attribute.
    pub fn denseI8ArrayGetElement(self: Attribute, pos: usize) i8 {
        return c.mlirDenseI8ArrayGetElement(self.handle, @intCast(pos));
    }

    /// Retrieves an i16 element from a DenseI16Array attribute.
    pub fn denseI16ArrayGetElement(self: Attribute, pos: usize) i16 {
        return c.mlirDenseI16ArrayGetElement(self.handle, @intCast(pos));
    }

    /// Retrieves an i32 element from a DenseI32Array attribute.
    pub fn denseI32ArrayGetElement(self: Attribute, pos: usize) i32 {
        return c.mlirDenseI32ArrayGetElement(self.handle, @intCast(pos));
    }

    /// Retrieves an i64 element from a DenseI64Array attribute.
    pub fn denseI64ArrayGetElement(self: Attribute, pos: usize) i64 {
        return c.mlirDenseI64ArrayGetElement(self.handle, @intCast(pos));
    }

    /// Retrieves an f32 element from a DenseF32Array attribute.
    pub fn denseF32ArrayGetElement(self: Attribute, pos: usize) f32 {
        return c.mlirDenseF32ArrayGetElement(self.handle, @intCast(pos));
    }

    /// Retrieves an f64 element from a DenseF64Array attribute.
    pub fn denseF64ArrayGetElement(self: Attribute, pos: usize) f64 {
        return c.mlirDenseF64ArrayGetElement(self.handle, @intCast(pos));
    }

    /// Retrieves the TypeID of a DenseElements attribute.
    pub fn denseElementsAttrGetTypeID() c.MlirTypeID {
        return c.mlirDenseElementsAttrGetTypeID();
    }

    /// Checks whether the attribute is a DenseElements attribute.
    pub fn isADenseElements(self: Attribute) bool {
        return c.mlirAttributeIsADenseElements(self.handle);
    }

    /// Checks whether the attribute is a DenseIntElements attribute.
    pub fn isADenseIntElements(self: Attribute) bool {
        return c.mlirAttributeIsADenseIntElements(self.handle);
    }

    /// Checks whether the attribute is a DenseFPElements attribute.
    pub fn isADenseFPElements(self: Attribute) bool {
        return c.mlirAttributeIsADenseFPElements(self.handle);
    }

    /// Retrieves the TypeID of a DenseIntOrFPElements attribute.
    pub fn denseIntOrFPElementsAttrGetTypeID() c.MlirTypeID {
        return c.mlirDenseIntOrFPElementsAttrGetTypeID();
    }

    /// Creates a DenseElements attribute from a list of Attributes.
    pub fn denseElementsAttrGet(shapedType: Type, elements: []const Attribute) Attribute {
        if (elements.len == 0) {
            return Attribute{ .handle = c.mlirDenseElementsAttrGet(shapedType.handle, 0, null) };
        } else {
            var tmp = SmallVector(c.MlirAttribute, 8).init(global_alloc);
            for (elements) |e| {
                tmp.push(e.handle);
            }
            return Attribute{
                .handle = c.mlirDenseElementsAttrGet(shapedType.handle, @intCast(elements.len), @ptrCast(tmp.slice())),
            };
        }
    }

    /// Creates a DenseElements attribute from a raw buffer.
    pub fn denseElementsAttrRawBufferGet(shapedType: Type, rawBuffer: []const u8) Attribute {
        if (rawBuffer.len == 0) {
            return Attribute{ .handle = c.mlirDenseElementsAttrRawBufferGet(shapedType.handle, 0, null) };
        } else {
            return Attribute{
                .handle = c.mlirDenseElementsAttrRawBufferGet(shapedType.handle, rawBuffer.len, rawBuffer.ptr),
            };
        }
    }

    /// Creates a splat DenseElements attribute from a single Attribute.
    pub fn denseElementsAttrSplatGet(shapedType: Type, element: Attribute) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrSplatGet(shapedType.handle, element.handle) };
    }

    /// Creates a splat DenseElements attribute from a boolean.
    pub fn denseElementsAttrBoolSplatGet(shapedType: Type, element: bool) Attribute {
        return Attribute{
            .handle = c.mlirDenseElementsAttrBoolSplatGet(shapedType.handle, if (element) 1 else 0),
        };
    }

    /// Creates a splat DenseElements attribute from a uint8.
    pub fn denseElementsAttrUInt8SplatGet(shapedType: Type, element: u8) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrUInt8SplatGet(shapedType.handle, element) };
    }

    /// Creates a splat DenseElements attribute from an int8.
    pub fn denseElementsAttrInt8SplatGet(shapedType: Type, element: i8) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrInt8SplatGet(shapedType.handle, element) };
    }

    /// Creates a splat DenseElements attribute from a uint32.
    pub fn denseElementsAttrUInt32SplatGet(shapedType: Type, element: u32) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrUInt32SplatGet(shapedType.handle, element) };
    }

    /// Creates a splat DenseElements attribute from an int32.
    pub fn denseElementsAttrInt32SplatGet(shapedType: Type, element: i32) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrInt32SplatGet(shapedType.handle, element) };
    }

    /// Creates a splat DenseElements attribute from a uint64.
    pub fn denseElementsAttrUInt64SplatGet(shapedType: Type, element: u64) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrUInt64SplatGet(shapedType.handle, element) };
    }

    /// Creates a splat DenseElements attribute from an int64.
    pub fn denseElementsAttrInt64SplatGet(shapedType: Type, element: i64) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrInt64SplatGet(shapedType.handle, element) };
    }

    /// Creates a splat DenseElements attribute from a float.
    pub fn denseElementsAttrFloatSplatGet(shapedType: Type, element: f32) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrFloatSplatGet(shapedType.handle, element) };
    }

    /// Creates a splat DenseElements attribute from a double.
    pub fn denseElementsAttrDoubleSplatGet(shapedType: Type, element: f64) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrDoubleSplatGet(shapedType.handle, element) };
    }

    /// Creates a splat DenseElements attribute from a string.
    pub fn denseElementsAttrStringSplatGet(shapedType: Type, element: StringRef) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrStringSplatGet(shapedType.handle, element.inner) };
    }

    /// Reshapes a DenseElements attribute to a new shape type.
    /// The total number of elements must remain the same.
    pub fn denseElementsAttrReshapeGet(self: Attribute, newShapedType: Type) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrReshapeGet(self.handle, newShapedType.handle) };
    }

    /// Checks whether the DenseElements attribute is a splat.
    pub fn denseElementsAttrIsSplat(self: Attribute) bool {
        return c.mlirDenseElementsAttrIsSplat(self.handle);
    }

    /// Retrieves the splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetSplatValue(self: Attribute) Attribute {
        return Attribute{ .handle = c.mlirDenseElementsAttrGetSplatValue(self.handle) };
    }

    /// Retrieves the boolean splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetBoolSplatValue(self: Attribute) bool {
        return c.mlirDenseElementsAttrGetBoolSplatValue(self.handle) != 0;
    }

    /// Retrieves the int8 splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetInt8SplatValue(self: Attribute) i8 {
        return c.mlirDenseElementsAttrGetInt8SplatValue(self.handle);
    }

    /// Retrieves the uint8 splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetUInt8SplatValue(self: Attribute) u8 {
        return c.mlirDenseElementsAttrGetUInt8SplatValue(self.handle);
    }

    /// Retrieves the int32 splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetInt32SplatValue(self: Attribute) i32 {
        return c.mlirDenseElementsAttrGetInt32SplatValue(self.handle);
    }

    /// Retrieves the uint32 splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetUInt32SplatValue(self: Attribute) u32 {
        return c.mlirDenseElementsAttrGetUInt32SplatValue(self.handle);
    }

    /// Retrieves the int64 splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetInt64SplatValue(self: Attribute) i64 {
        return c.mlirDenseElementsAttrGetInt64SplatValue(self.handle);
    }

    /// Retrieves the uint64 splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetUInt64SplatValue(self: Attribute) u64 {
        return c.mlirDenseElementsAttrGetUInt64SplatValue(self.handle);
    }

    /// Retrieves the float splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetFloatSplatValue(self: Attribute) f32 {
        return c.mlirDenseElementsAttrGetFloatSplatValue(self.handle);
    }

    /// Retrieves the double splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetDoubleSplatValue(self: Attribute) f64 {
        return c.mlirDenseElementsAttrGetDoubleSplatValue(self.handle);
    }

    /// Retrieves the string splat value from a DenseElements attribute.
    pub fn denseElementsAttrGetStringSplatValue(self: Attribute) StringRef {
        return StringRef{ .inner = c.mlirDenseElementsAttrGetStringSplatValue(self.handle) };
    }

    /// Retrieves a boolean value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetBoolValue(self: Attribute, pos: usize) bool {
        return c.mlirDenseElementsAttrGetBoolValue(self.handle, @intCast(pos)) != 0;
    }

    /// Retrieves an int8 value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetInt8Value(self: Attribute, pos: usize) i8 {
        return c.mlirDenseElementsAttrGetInt8Value(self.handle, @intCast(pos));
    }

    /// Retrieves a uint8 value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetUInt8Value(self: Attribute, pos: usize) u8 {
        return c.mlirDenseElementsAttrGetUInt8Value(self.handle, @intCast(pos));
    }

    /// Retrieves an int16 value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetInt16Value(self: Attribute, pos: usize) i16 {
        return c.mlirDenseElementsAttrGetInt16Value(self.handle, @intCast(pos));
    }

    /// Retrieves a uint16 value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetUInt16Value(self: Attribute, pos: usize) u16 {
        return c.mlirDenseElementsAttrGetUInt16Value(self.handle, @intCast(pos));
    }

    /// Retrieves an int32 value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetInt32Value(self: Attribute, pos: usize) i32 {
        return c.mlirDenseElementsAttrGetInt32Value(self.handle, @intCast(pos));
    }

    /// Retrieves a uint32 value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetUInt32Value(self: Attribute, pos: usize) u32 {
        return c.mlirDenseElementsAttrGetUInt32Value(self.handle, @intCast(pos));
    }

    /// Retrieves an int64 value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetInt64Value(self: Attribute, pos: usize) i64 {
        return c.mlirDenseElementsAttrGetInt64Value(self.handle, @intCast(pos));
    }

    /// Retrieves a uint64 value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetUInt64Value(self: Attribute, pos: usize) u64 {
        return c.mlirDenseElementsAttrGetUInt64Value(self.handle, @intCast(pos));
    }

    /// Retrieves a float value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetFloatValue(self: Attribute, pos: usize) f32 {
        return c.mlirDenseElementsAttrGetFloatValue(self.handle, @intCast(pos));
    }

    /// Retrieves a double value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetDoubleValue(self: Attribute, pos: usize) f64 {
        return c.mlirDenseElementsAttrGetDoubleValue(self.handle, @intCast(pos));
    }

    /// Retrieves a string value at a specific position in a DenseElements attribute.
    pub fn denseElementsAttrGetStringValue(self: Attribute, pos: usize) StringRef {
        return StringRef{ .inner = c.mlirDenseElementsAttrGetStringValue(self.handle, @intCast(pos)) };
    }

    /// Retrieves the raw data buffer from a DenseElements attribute.
    /// **Caution:** The size of the buffer must be inferred from the attribute's type.
    pub fn denseElementsAttrGetRawData(self: Attribute) ?[]const u8 {
        const ptr = c.mlirDenseElementsAttrGetRawData(self.handle);
        if (ptr == null) return null;
        // Without size information, it's not possible to create a proper slice.
        // Users must manage this based on the attribute's type and shape.
        return null; // Placeholder: implement as needed.
    }

    /// Checks whether the attribute is a DenseResourceElements attribute.
    pub fn isADenseResourceElements(self: Attribute) bool {
        return c.mlirAttributeIsADenseResourceElements(self.handle);
    }

    // /// Creates an unmanaged DenseResourceElements attribute with raw data and a deleter.
    // pub fn unmanagedDenseResourceElementsAttrGet(
    //     shapedType: Type,
    //     name: StringRef,
    //     data: []const u8,
    //     dataAlignment: usize,
    //     dataIsMutable: bool,
    //     deleter: ?fn(userData: *c_void, data: ?* u8, size: usize, align: usize) callconv(.c) void,
    //     userData: *anyopaque
    // ) Attribute {
    //     if (data.len == 0) {
    //         return Attribute{
    //             .handle = c.mlirUnmanagedDenseResourceElementsAttrGet(
    //                 shapedType.handle,
    //                 name.inner,
    //                 null,
    //                 0,
    //                 @intCast(dataAlignment),
    //                 dataIsMutable,
    //                 @ptrCast(deleter),
    //                 userData
    //             ),
    //         };
    //     } else {
    //         return Attribute{
    //             .handle = c.mlirUnmanagedDenseResourceElementsAttrGet(
    //                 shapedType.handle,
    //                 name.inner,
    //                 @ptrCast(* c_char, data.ptr),
    //                 @intCast(size_t, data.len),
    //                 @intCast(size_t, dataAlignment),
    //                 dataIsMutable,
    //                 @ptrCast(* c_void, deleter),
    //                 userData
    //             ),
    //         };
    //     }
    // }

    /// Creates an unmanaged DenseBoolResourceElements attribute.
    pub fn unmanagedDenseBoolResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const bool) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseBoolResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(c.int, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(if (v) 1 else 0);
            }

            return Attribute{
                .handle = c.mlirUnmanagedDenseBoolResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseUInt8ResourceElements attribute.
    pub fn unmanagedDenseUInt8ResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const u8) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseUInt8ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(u8, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirUnmanagedDenseUInt8ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseInt8ResourceElements attribute.
    pub fn unmanagedDenseInt8ResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const i8) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseInt8ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(i8, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirUnmanagedDenseInt8ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseUInt16ResourceElements attribute.
    pub fn unmanagedDenseUInt16ResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const u16) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseUInt16ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(u16, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }

            return Attribute{
                .handle = c.mlirUnmanagedDenseUInt16ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseInt16ResourceElements attribute.
    pub fn unmanagedDenseInt16ResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const i16) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseInt16ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(i16, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }

            return Attribute{
                .handle = c.mlirUnmanagedDenseInt16ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseUInt32ResourceElements attribute.
    pub fn unmanagedDenseUInt32ResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const u32) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseUInt32ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(u32, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirUnmanagedDenseUInt32ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseInt32ResourceElements attribute.
    pub fn unmanagedDenseInt32ResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const i32) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseInt32ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(i32, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirUnmanagedDenseInt32ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseUInt64ResourceElements attribute.
    pub fn unmanagedDenseUInt64ResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const u64) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseUInt64ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(u64, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirUnmanagedDenseUInt64ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseInt64ResourceElements attribute.
    pub fn unmanagedDenseInt64ResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const i64) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseInt64ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(i64, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirUnmanagedDenseInt64ResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseF32ResourceElements attribute.
    pub fn unmanagedDenseFloatResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const f32) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseFloatResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(f32, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirUnmanagedDenseFloatResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Creates an unmanaged DenseDoubleResourceElements attribute.
    pub fn unmanagedDenseDoubleResourceElementsAttrGet(shapedType: Type, name: StringRef, numElements: usize, elements: []const f64) Attribute {
        if (numElements == 0) {
            return Attribute{
                .handle = c.mlirUnmanagedDenseDoubleResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    0,
                    null,
                ),
            };
        } else {
            var tmp = SmallVector(f64, 8).init(global_alloc);
            for (elements) |v| {
                tmp.push(v);
            }
            return Attribute{
                .handle = c.mlirUnmanagedDenseDoubleResourceElementsAttrGet(
                    shapedType.handle,
                    name.inner,
                    @intCast(numElements),
                    tmp,
                ),
            };
        }
    }

    /// Retrieves a boolean value at a specific position in a DenseResourceElements attribute.
    pub fn denseBoolResourceElementsAttrGetValue(self: Attribute, pos: usize) bool {
        return c.mlirDenseBoolResourceElementsAttrGetValue(self.handle, @intCast(pos)) != 0;
    }

    /// Retrieves an int8 value at a specific position in a DenseResourceElements attribute.
    pub fn denseInt8ResourceElementsAttrGetValue(self: Attribute, pos: usize) i8 {
        return c.mlirDenseInt8ResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves a uint8 value at a specific position in a DenseResourceElements attribute.
    pub fn denseUInt8ResourceElementsAttrGetValue(self: Attribute, pos: usize) u8 {
        return c.mlirDenseUInt8ResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves an int16 value at a specific position in a DenseResourceElements attribute.
    pub fn denseInt16ResourceElementsAttrGetValue(self: Attribute, pos: usize) i16 {
        return c.mlirDenseInt16ResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves a uint16 value at a specific position in a DenseResourceElements attribute.
    pub fn denseUInt16ResourceElementsAttrGetValue(self: Attribute, pos: usize) u16 {
        return c.mlirDenseUInt16ResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves an int32 value at a specific position in a DenseResourceElements attribute.
    pub fn denseInt32ResourceElementsAttrGetValue(self: Attribute, pos: usize) i32 {
        return c.mlirDenseInt32ResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves a uint32 value at a specific position in a DenseResourceElements attribute.
    pub fn denseUInt32ResourceElementsAttrGetValue(self: Attribute, pos: usize) u32 {
        return c.mlirDenseUInt32ResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves an int64 value at a specific position in a DenseResourceElements attribute.
    pub fn denseInt64ResourceElementsAttrGetValue(self: Attribute, pos: usize) i64 {
        return c.mlirDenseInt64ResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves a uint64 value at a specific position in a DenseResourceElements attribute.
    pub fn denseUInt64ResourceElementsAttrGetValue(self: Attribute, pos: usize) u64 {
        return c.mlirDenseUInt64ResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves a float value at a specific position in a DenseResourceElements attribute.
    pub fn denseFloatResourceElementsAttrGetValue(self: Attribute, pos: usize) f32 {
        return c.mlirDenseFloatResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }

    /// Retrieves a double value at a specific position in a DenseResourceElements attribute.
    pub fn denseDoubleResourceElementsAttrGetValue(self: Attribute, pos: usize) f64 {
        return c.mlirDenseDoubleResourceElementsAttrGetValue(self.handle, @intCast(pos));
    }
};

/// The main `Type` wrapper, holding the underlying `MlirType`.
pub const Type = struct {
    handle: c.MlirType,

    pub fn empty() Type {
        return Type{ .handle = c.MlirType{} };
    }

    pub fn parseGet(ctx: Context, typeStr: StringRef) Type {
        return Type{ .handle = c.mlirTypeParseGet(ctx.handle, typeStr.inner) };
    }

    pub fn getContext(self: *Type) Context {
        return Context{ .handle = c.mlirTypeGetContext(self.handle) };
    }

    pub fn getTypeID(self: *Type) c.MlirTypeID {
        return c.mlirTypeGetTypeID(self.handle);
    }

    pub fn getDialect(self: *Type) Dialect {
        return Dialect{ .handle = c.mlirTypeGetDialect(self.handle) };
    }

    pub fn isNull(self: *const Type) bool {
        return c.mlirTypeIsNull(self.handle);
    }

    pub fn equal(self: *const Type, other: Type) bool {
        return c.mlirTypeEqual(self.handle, other.handle);
    }

    pub fn print(self: *const Type, cb: fn (c.MlirStringRef, ?*anyopaque) callconv(.c) void, userData: ?*anyopaque) void {
        c.mlirTypePrint(self.handle, cb, userData);
    }

    pub fn dump(self: *const Type) void {
        c.mlirTypeDump(self.handle);
    }
    /// Returns a special "null" (empty) type.
    pub fn getNull() Type {
        return Type{ .handle = c.mlirTypeGetNull() };
    }

    /// Checks whether the type is a Location type.
    pub fn isALocation(self: Type) bool {
        return c.mlirTypeIsALocation(self.handle);
    }

    /// =============================
    /// Integer Types
    /// =============================
    /// Returns the typeID of an Integer type.
    pub fn getIntegerTypeID() c.MlirTypeID {
        return c.mlirIntegerTypeGetTypeID();
    }

    /// Checks whether the given type is an integer type.
    pub fn isAInteger(self: Type) bool {
        return c.mlirTypeIsAInteger(self.handle);
    }

    /// Creates a signless integer type of the given bitwidth in the context.
    pub fn getSignlessIntegerType(ctx: Context, bitwidth: u32) Type {
        return Type{ .handle = c.mlirIntegerTypeGet(ctx.handle, bitwidth) };
    }

    /// Creates a signed integer type of the given bitwidth in the context.
    pub fn getSignedIntegerType(ctx: Context, bitwidth: u32) Type {
        return Type{ .handle = c.mlirIntegerTypeSignedGet(ctx.handle, bitwidth) };
    }

    /// Creates an unsigned integer type of the given bitwidth in the context.
    pub fn getUnsignedIntegerType(ctx: Context, bitwidth: u32) Type {
        return Type{ .handle = c.mlirIntegerTypeUnsignedGet(ctx.handle, bitwidth) };
    }

    /// Returns the bitwidth of an integer type.
    pub fn getIntegerBitwidth(self: Type) u32 {
        return c.mlirIntegerTypeGetWidth(self.handle);
    }

    /// Checks whether the given integer type is signless.
    pub fn isIntegerSignless(self: Type) bool {
        return c.mlirIntegerTypeIsSignless(self.handle);
    }

    /// Checks whether the given integer type is signed.
    pub fn isIntegerSigned(self: Type) bool {
        return c.mlirIntegerTypeIsSigned(self.handle);
    }

    /// Checks whether the given integer type is unsigned.
    pub fn isIntegerUnsigned(self: Type) bool {
        return c.mlirIntegerTypeIsUnsigned(self.handle);
    }

    /// =============================
    /// Index Type
    /// =============================
    /// Returns the typeID of an Index type.
    pub fn getIndexTypeID() c.MlirTypeID {
        return c.mlirIndexTypeGetTypeID();
    }

    /// Checks whether the given type is an index type.
    pub fn isAIndex(self: Type) bool {
        return c.mlirTypeIsAIndex(self.handle);
    }

    /// Creates an index type in the given context.
    pub fn getIndexType(ctx: Context) Type {
        return Type{ .handle = c.mlirIndexTypeGet(ctx.handle) };
    }

    /// =============================
    /// Floating-point Types
    /// =============================
    /// Checks whether the given type is a floating-point type.
    pub fn isAFloat(self: Type) bool {
        return c.mlirTypeIsAFloat(self.handle);
    }

    /// Returns the bitwidth of a floating-point type.
    pub fn getFloatBitwidth(self: Type) u32 {
        return c.mlirFloatTypeGetWidth(self.handle);
    }

    /// =============================
    /// Specific Floating-point Types
    /// =============================
    /// Float4E2M1FN Type
    pub fn getFloat4E2M1FNTypeID() c.MlirTypeID {
        return c.mlirFloat4E2M1FNTypeGetTypeID();
    }

    pub fn isAFloat4E2M1FN(self: Type) bool {
        return c.mlirTypeIsAFloat4E2M1FN(self.handle);
    }

    pub fn getFloat4E2M1FNType(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat4E2M1FNTypeGet(ctx.handle) };
    }

    /// Float6E2M3FN Type
    pub fn getFloat6E2M3FNTypeID() c.MlirTypeID {
        return c.mlirFloat6E2M3FNTypeGetTypeID();
    }

    pub fn isAFloat6E2M3FN(self: Type) bool {
        return c.mlirTypeIsAFloat6E2M3FN(self.handle);
    }

    pub fn getFloat6E2M3FNType(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat6E2M3FNTypeGet(ctx.handle) };
    }

    /// Float6E3M2FN Type
    pub fn getFloat6E3M2FNTypeID() c.MlirTypeID {
        return c.mlirFloat6E3M2FNTypeGetTypeID();
    }

    pub fn isAFloat6E3M2FN(self: Type) bool {
        return c.mlirTypeIsAFloat6E3M2FN(self.handle);
    }

    pub fn getFloat6E3M2FNType(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat6E3M2FNTypeGet(ctx.handle) };
    }

    /// Float8E5M2 Type
    pub fn getFloat8E5M2TypeID() c.MlirTypeID {
        return c.mlirFloat8E5M2TypeGetTypeID();
    }

    pub fn isAFloat8E5M2(self: Type) bool {
        return c.mlirTypeIsAFloat8E5M2(self.handle);
    }

    pub fn getFloat8E5M2Type(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat8E5M2TypeGet(ctx.handle) };
    }

    /// Float8E4M3 Type
    pub fn getFloat8E4M3TypeID() c.MlirTypeID {
        return c.mlirFloat8E4M3TypeGetTypeID();
    }

    pub fn isAFloat8E4M3(self: Type) bool {
        return c.mlirTypeIsAFloat8E4M3(self.handle);
    }

    pub fn getFloat8E4M3Type(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat8E4M3TypeGet(ctx.handle) };
    }

    /// Float8E4M3FN Type
    pub fn getFloat8E4M3FNTypeID() c.MlirTypeID {
        return c.mlirFloat8E4M3FNTypeGetTypeID();
    }

    pub fn isAFloat8E4M3FN(self: Type) bool {
        return c.mlirTypeIsAFloat8E4M3FN(self.handle);
    }

    pub fn getFloat8E4M3FNType(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat8E4M3FNTypeGet(ctx.handle) };
    }

    /// Float8E5M2FNUZ Type
    pub fn getFloat8E5M2FNUZTypeID() c.MlirTypeID {
        return c.mlirFloat8E5M2FNUZTypeGetTypeID();
    }

    pub fn isAFloat8E5M2FNUZ(self: Type) bool {
        return c.mlirTypeIsAFloat8E5M2FNUZ(self.handle);
    }

    pub fn getFloat8E5M2FNUZType(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat8E5M2FNUZTypeGet(ctx.handle) };
    }

    /// Float8E4M3FNUZ Type
    pub fn getFloat8E4M3FNUZTypeID() c.MlirTypeID {
        return c.mlirFloat8E4M3FNUZTypeGetTypeID();
    }

    pub fn isAFloat8E4M3FNUZ(self: Type) bool {
        return c.mlirTypeIsAFloat8E4M3FNUZ(self.handle);
    }

    pub fn getFloat8E4M3FNUZType(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat8E4M3FNUZTypeGet(ctx.handle) };
    }

    /// Float8E4M3B11FNUZ Type
    pub fn getFloat8E4M3B11FNUZTypeID() c.MlirTypeID {
        return c.mlirFloat8E4M3B11FNUZTypeGetTypeID();
    }

    pub fn isAFloat8E4M3B11FNUZ(self: Type) bool {
        return c.mlirTypeIsAFloat8E4M3B11FNUZ(self.handle);
    }

    pub fn getFloat8E4M3B11FNUZType(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat8E4M3B11FNUZTypeGet(ctx.handle) };
    }

    /// Float8E3M4 Type
    pub fn getFloat8E3M4TypeID() c.MlirTypeID {
        return c.mlirFloat8E3M4TypeGetTypeID();
    }

    pub fn isAFloat8E3M4(self: Type) bool {
        return c.mlirTypeIsAFloat8E3M4(self.handle);
    }

    pub fn getFloat8E3M4Type(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat8E3M4TypeGet(ctx.handle) };
    }

    /// Float8E8M0FNU Type
    pub fn getFloat8E8M0FNUTypeID() c.MlirTypeID {
        return c.mlirFloat8E8M0FNUTypeGetTypeID();
    }

    pub fn isAFloat8E8M0FNU(self: Type) bool {
        return c.mlirTypeIsAFloat8E8M0FNU(self.handle);
    }

    pub fn getFloat8E8M0FNUType(ctx: Context) Type {
        return Type{ .handle = c.mlirFloat8E8M0FNUTypeGet(ctx.handle) };
    }

    /// BFloat16 Type
    pub fn getBFloat16TypeID() c.MlirTypeID {
        return c.mlirBFloat16TypeGetTypeID();
    }

    pub fn isABFloat16(self: Type) bool {
        return c.mlirTypeIsABF16(self.handle);
    }

    pub fn getBFloat16Type(ctx: Context) Type {
        return Type{ .handle = c.mlirBF16TypeGet(ctx.handle) };
    }

    /// Float16 Type
    pub fn getFloat16TypeID() c.MlirTypeID {
        return c.mlirFloat16TypeGetTypeID();
    }

    pub fn isAFloat16(self: Type) bool {
        return c.mlirTypeIsAF16(self.handle);
    }

    pub fn getFloat16Type(ctx: Context) Type {
        return Type{ .handle = c.mlirF16TypeGet(ctx.handle) };
    }

    /// Float32 Type
    pub fn getFloat32TypeID() c.MlirTypeID {
        return c.mlirFloat32TypeGetTypeID();
    }

    pub fn isAFloat32(self: Type) bool {
        return c.mlirTypeIsAF32(self.handle);
    }

    pub fn getFloat32Type(ctx: Context) Type {
        return Type{ .handle = c.mlirF32TypeGet(ctx.handle) };
    }

    /// Float64 Type
    pub fn getFloat64TypeID() c.MlirTypeID {
        return c.mlirFloat64TypeGetTypeID();
    }

    pub fn isAFloat64(self: Type) bool {
        return c.mlirTypeIsAF64(self.handle);
    }

    pub fn getFloat64Type(ctx: Context) Type {
        return Type{ .handle = c.mlirF64TypeGet(ctx.handle) };
    }

    /// TF32 Type
    pub fn getTF32TypeID() c.MlirTypeID {
        return c.mlirFloatTF32TypeGetTypeID();
    }

    pub fn isATF32(self: Type) bool {
        return c.mlirTypeIsATF32(self.handle);
    }

    pub fn getTF32Type(ctx: Context) Type {
        return Type{ .handle = c.mlirTF32TypeGet(ctx.handle) };
    }

    /// =============================
    /// None Type
    /// =============================
    /// Returns the typeID of a None type.
    pub fn getNoneTypeID() c.MlirTypeID {
        return c.mlirNoneTypeGetTypeID();
    }

    /// Checks whether the given type is a None type.
    pub fn isANone(self: Type) bool {
        return c.mlirTypeIsANone(self.handle);
    }

    /// Creates a None type in the given context.
    pub fn getNoneType(ctx: Context) Type {
        return Type{ .handle = c.mlirNoneTypeGet(ctx.handle) };
    }

    /// =============================
    /// Complex Type
    /// =============================
    /// Returns the typeID of a Complex type.
    pub fn getComplexTypeID() c.MlirTypeID {
        return c.mlirComplexTypeGetTypeID();
    }

    /// Checks whether the given type is a Complex type.
    pub fn isAComplex(self: Type) bool {
        return c.mlirTypeIsAComplex(self.handle);
    }

    /// Creates a complex type with the given element type.
    pub fn getComplexType(elementType: Type) Type {
        return Type{ .handle = c.mlirComplexTypeGet(elementType.handle) };
    }

    /// Returns the element type of the given complex type.
    pub fn getComplexElementType(self: Type) Type {
        return Type{ .handle = c.mlirComplexTypeGetElementType(self.handle) };
    }

    /// =============================
    /// Shaped Type
    /// =============================
    /// Checks whether the given type is a Shaped type.
    pub fn isAShaped(self: Type) bool {
        return c.mlirTypeIsAShaped(self.handle);
    }

    /// Returns the element type of the shaped type.
    pub fn getShapedElementType(self: Type) Type {
        return Type{ .handle = c.mlirShapedTypeGetElementType(self.handle) };
    }

    /// Checks whether the given shaped type is ranked.
    pub fn hasRank(self: Type) bool {
        return c.mlirShapedTypeHasRank(self.handle);
    }

    /// Returns the rank of the given ranked shaped type.
    pub fn getRank(self: Type) i64 {
        return c.mlirShapedTypeGetRank(self.handle);
    }

    /// Checks whether the given shaped type has a static shape.
    pub fn hasStaticShape(self: Type) bool {
        return c.mlirShapedTypeHasStaticShape(self.handle);
    }

    /// Checks whether the dim-th dimension of the given shaped type is dynamic.
    pub fn isDimDynamic(self: Type, dim: isize) bool {
        return c.mlirShapedTypeIsDynamicDim(self.handle, dim);
    }

    /// Returns the dim-th dimension of the given ranked shaped type.
    pub fn getDimSize(self: Type, dim: isize) i64 {
        return c.mlirShapedTypeGetDimSize(self.handle, dim);
    }

    /// Checks whether the given value is used as a placeholder for dynamic sizes
    /// in shaped types.
    pub fn isDynamicSize(size: i64) bool {
        return c.mlirShapedTypeIsDynamicSize(size);
    }

    /// Returns the value indicating a dynamic size in a shaped type.
    pub fn getDynamicSize() i64 {
        return c.mlirShapedTypeGetDynamicSize();
    }

    /// Checks whether the given value is used as a placeholder for dynamic strides
    /// and offsets in shaped types.
    pub fn isDynamicStrideOrOffset(val: i64) bool {
        return c.mlirShapedTypeIsDynamicStrideOrOffset(val);
    }

    /// Returns the value indicating a dynamic stride or offset in a shaped type.
    pub fn getDynamicStrideOrOffset() i64 {
        return c.mlirShapedTypeGetDynamicStrideOrOffset();
    }

    /// =============================
    /// Vector Type
    /// =============================
    /// Returns the typeID of a Vector type.
    pub fn getVectorTypeID() c.MlirTypeID {
        return c.mlirVectorTypeGetTypeID();
    }

    /// Checks whether the given type is a Vector type.
    pub fn isAVector(self: Type) bool {
        return c.mlirTypeIsAVector(self.handle);
    }

    /// Creates a vector type with the given rank, shape, and element type.
    pub fn getVectorType(rank: isize, shape: []const i64, elementType: Type) Type {
        return Type{
            .handle = c.mlirVectorTypeGet(rank, shape.ptr, elementType.handle),
        };
    }

    /// Creates a vector type with scalability information.
    pub fn getScalableVectorType(rank: isize, shape: []const i64, scalable: []const bool, elementType: Type) Type {
        return Type{
            .handle = c.mlirVectorTypeGetScalable(
                rank,
                shape.ptr,
                scalable.ptr,
                elementType.handle,
            ),
        };
    }

    /// Checks whether the given vector type is scalable.
    pub fn isVectorScalable(self: Type) bool {
        return c.mlirVectorTypeIsScalable(self.handle);
    }

    /// Checks whether the dim-th dimension of the given vector is scalable.
    pub fn isVectorDimScalable(self: Type, dim: isize) bool {
        return c.mlirVectorTypeIsDimScalable(self.handle, dim);
    }

    /// =============================
    /// Tensor Types
    /// =============================
    /// Checks whether the given type is a Tensor type.
    pub fn isATensor(self: Type) bool {
        return c.mlirTypeIsATensor(self.handle);
    }

    /// Returns the typeID of a RankedTensor type.
    pub fn getRankedTensorTypeID() c.MlirTypeID {
        return c.mlirRankedTensorTypeGetTypeID();
    }

    /// Checks whether the given type is a ranked tensor type.
    pub fn isARankedTensor(self: Type) bool {
        return c.mlirTypeIsARankedTensor(self.handle);
    }

    /// Returns the typeID of an UnrankedTensor type.
    pub fn getUnrankedTensorTypeID() c.MlirTypeID {
        return c.mlirUnrankedTensorTypeGetTypeID();
    }

    /// Checks whether the given type is an unranked tensor type.
    pub fn isAUnrankedTensor(self: Type) bool {
        return c.mlirTypeIsAUnrankedTensor(self.handle);
    }

    /// Creates a ranked tensor type with the given rank, shape, element type, and optional encoding.
    pub fn getRankedTensorType(rank: isize, shape: []const i64, elementType: Type, encoding: Attribute) Type {
        return Type{
            .handle = c.mlirRankedTensorTypeGet(
                rank,
                shape.ptr,
                elementType.handle,
                encoding.handle,
            ),
        };
    }

    /// Creates a ranked tensor type with checked diagnostics.
    pub fn getRankedTensorTypeChecked(loc: c.MlirLocation, rank: isize, shape: []const i64, elementType: Type, encoding: Attribute) ?Type {
        const result = c.mlirRankedTensorTypeGetChecked(
            loc,
            rank,
            shape.ptr,
            elementType.handle,
            encoding.handle,
        );
        if (result.ptr == null) return null;
        return Type{ .handle = result };
    }

    /// Retrieves the 'encoding' attribute from the ranked tensor type.
    pub fn getRankedTensorEncoding(self: Type) Attribute {
        return Attribute{ .handle = c.mlirRankedTensorTypeGetEncoding(self.handle) };
    }

    /// Creates an unranked tensor type with the given element type.
    pub fn getUnrankedTensorType(elementType: Type) Type {
        return Type{ .handle = c.mlirUnrankedTensorTypeGet(elementType.handle) };
    }

    /// Creates an unranked tensor type with checked diagnostics.
    pub fn getUnrankedTensorTypeChecked(loc: c.MlirLocation, elementType: Type) ?Type {
        const result = c.mlirUnrankedTensorTypeGetChecked(loc, elementType.handle);
        if (result.ptr == null) return null;
        return Type{ .handle = result };
    }

    /// =============================
    /// MemRef Types
    /// =============================
    /// Returns the typeID of a MemRef type.
    pub fn getMemRefTypeID() c.MlirTypeID {
        return c.mlirMemRefTypeGetTypeID();
    }

    /// Checks whether the given type is a MemRef type.
    pub fn isAMemRef(self: *Type) bool {
        return c.mlirTypeIsAMemRef(self.handle);
    }

    /// Returns the typeID of an UnrankedMemRef type.
    pub fn getUnrankedMemRefTypeID() c.MlirTypeID {
        return c.mlirUnrankedMemRefTypeGetTypeID();
    }

    /// Checks whether the given type is an UnrankedMemRef type.
    pub fn isAUnrankedMemRef(self: Type) bool {
        return c.mlirTypeIsAUnrankedMemRef(self.handle);
    }

    /// Creates a MemRef type with the given rank, shape, layout, and memory space.
    pub fn getMemRefType(elementType: Type, rank: isize, shape: []const i64, layout: Attribute, memorySpace: Type.Attribute) Type {
        return Type{
            .handle = c.mlirMemRefTypeGet(
                elementType.handle,
                rank,
                shape.ptr,
                layout.handle,
                memorySpace.handle,
            ),
        };
    }

    /// Creates a MemRef type with checked diagnostics.
    pub fn getMemRefTypeChecked(loc: c.MlirLocation, elementType: Type, rank: isize, shape: []const i64, layout: Attribute, memorySpace: Type.Attribute) ?Type {
        const result = c.mlirMemRefTypeGetChecked(
            loc,
            elementType.handle,
            rank,
            shape.ptr,
            layout.handle,
            memorySpace.handle,
        );
        if (result.ptr == null) return null;
        return Type{ .handle = result };
    }

    /// Creates a contiguous MemRef type with the given rank, shape, and memory space.
    pub fn getContiguousMemRefType(elementType: Type, rank: isize, shape: []const i64, memorySpace: Attribute) Type {
        return Type{
            .handle = c.mlirMemRefTypeContiguousGet(
                elementType.handle,
                rank,
                shape.ptr,
                memorySpace.handle,
            ),
        };
    }

    /// Creates a contiguous MemRef type with checked diagnostics.
    pub fn getContiguousMemRefTypeChecked(loc: c.MlirLocation, elementType: Type, rank: isize, shape: []const i64, memorySpace: Attribute) ?Type {
        const result = c.mlirMemRefTypeContiguousGetChecked(
            loc,
            elementType.handle,
            rank,
            shape.ptr,
            memorySpace.handle,
        );
        if (result.ptr == null) return null;
        return Type{ .handle = result };
    }

    /// Creates an Unranked MemRef type with the given element type and memory space.
    pub fn getUnrankedMemRefType(elementType: Type, memorySpace: Attribute) Type {
        return Type{
            .handle = c.mlirUnrankedMemRefTypeGet(elementType.handle, memorySpace.handle),
        };
    }

    /// Creates an Unranked MemRef type with checked diagnostics.
    pub fn getUnrankedMemRefTypeChecked(loc: c.MlirLocation, elementType: Type, memorySpace: Attribute) ?Type {
        const result = c.mlirUnrankedMemRefTypeGetChecked(loc, elementType.handle, memorySpace.handle);
        if (result.ptr == null) return null;
        return Type{ .handle = result };
    }

    /// Retrieves the layout attribute from a MemRef type.
    pub fn getMemRefLayout(self: Type) Attribute {
        return Attribute{ .handle = c.mlirMemRefTypeGetLayout(self.handle) };
    }

    /// Retrieves the affine map from a MemRef type.
    pub fn getMemRefAffineMap(self: Type) c.MlirAffineMap {
        return c.mlirMemRefTypeGetAffineMap(self.handle);
    }

    /// Retrieves the memory space attribute from a MemRef type.
    pub fn getMemRefMemorySpace(self: Type) Attribute {
        return Attribute{ .handle = c.mlirMemRefTypeGetMemorySpace(self.handle) };
    }

    /// Retrieves the strides and offset from a MemRef type.
    pub fn getMemRefStridesAndOffset(self: Type, strides: []i64, offset: *i64) c.MlirLogicalResult {
        return c.mlirMemRefTypeGetStridesAndOffset(
            self.handle,
            strides.ptr,
            offset,
        );
    }

    /// Retrieves the memory space from an Unranked MemRef type.
    pub fn getUnrankedMemRefMemorySpace(self: Type) Attribute {
        return Attribute{ .handle = c.mlirUnrankedMemrefGetMemorySpace(self.handle) };
    }

    /// =============================
    /// Tuple Type
    /// =============================
    /// Returns the typeID of a Tuple type.
    pub fn getTupleTypeID() c.MlirTypeID {
        return c.mlirTupleTypeGetTypeID();
    }

    /// Checks whether the given type is a Tuple type.
    pub fn isATuple(self: Type) bool {
        return c.mlirTypeIsATuple(self.handle);
    }

    /// Creates a Tuple type from a list of element types.
    pub fn getTupleType(ctx: Context, numElements: isize, elements: []const Type) Type {
        return Type{
            .handle = c.mlirTupleTypeGet(ctx.handle, numElements, elements.ptr),
        };
    }

    /// Retrieves the number of types contained in a Tuple.
    pub fn getTupleNumTypes(self: Type) isize {
        return c.mlirTupleTypeGetNumTypes(self.handle);
    }

    /// Retrieves the pos-th type in the Tuple.
    pub fn getTupleTypeAt(self: Type, pos: isize) Type {
        return Type{
            .handle = c.mlirTupleTypeGetType(self.handle, pos),
        };
    }

    /// =============================
    /// Function Type
    /// =============================
    /// Returns the typeID of a Function type.
    pub fn getFunctionTypeID() c.MlirTypeID {
        return c.mlirFunctionTypeGetTypeID();
    }

    /// Checks whether the given type is a Function type.
    pub fn isAFunction(self: Type) bool {
        return c.mlirTypeIsAFunction(self.handle);
    }

    /// Creates a Function type from input and result types.
    pub fn getFunctionType(ctx: Context, numInputs: isize, inputs: []const Type, numResults: isize, results: []const Type) Type {
        return Type{
            .handle = c.mlirFunctionTypeGet(
                ctx.handle,
                numInputs,
                @ptrCast(inputs),
                numResults,
                @ptrCast(results),
            ),
        };
    }

    /// Retrieves the number of input types in a Function type.
    pub fn getFunctionNumInputs(self: Type) isize {
        return c.mlirFunctionTypeGetNumInputs(self.handle);
    }

    /// Retrieves the number of result types in a Function type.
    pub fn getFunctionNumResults(self: Type) isize {
        return c.mlirFunctionTypeGetNumResults(self.handle);
    }

    /// Retrieves the pos-th input type in a Function type.
    pub fn getFunctionInput(self: Type, pos: isize) Type {
        return Type{
            .handle = c.mlirFunctionTypeGetInput(self.handle, pos),
        };
    }

    /// Retrieves the pos-th result type in a Function type.
    pub fn getFunctionResult(self: Type, pos: isize) Type {
        return Type{
            .handle = c.mlirFunctionTypeGetResult(self.handle, pos),
        };
    }

    /// =============================
    /// Opaque Type
    /// =============================
    /// Returns the typeID of an Opaque type.
    pub fn getOpaqueTypeID() c.MlirTypeID {
        return c.mlirOpaqueTypeGetTypeID();
    }

    /// Checks whether the given type is an Opaque type.
    pub fn isAOpaque(self: Type) bool {
        return c.mlirTypeIsAOpaque(self.handle);
    }

    /// Creates an Opaque type with the given dialect namespace and type data.
    pub fn getOpaqueType(ctx: Context, dialectNamespace: StringRef, typeData: StringRef) Type {
        return Type{
            .handle = c.mlirOpaqueTypeGet(
                ctx.handle,
                dialectNamespace.inner,
                typeData.inner,
            ),
        };
    }

    /// Retrieves the dialect namespace from an Opaque type.
    pub fn getOpaqueDialectNamespace(self: Type) StringRef {
        return StringRef{ .inner = c.mlirOpaqueTypeGetDialectNamespace(self.handle) };
    }

    /// Retrieves the raw data from an Opaque type.
    pub fn getOpaqueData(self: Type) StringRef {
        return StringRef{ .inner = c.mlirOpaqueTypeGetData(self.handle) };
    }
};

/// =============================
/// Diagnostic Severity Enum
/// =============================
pub const DiagnosticSeverity = enum(c_int) {
    Error = c.MlirDiagnosticSeverity.MlirDiagnosticError,
    Warning = c.MlirDiagnosticSeverity.MlirDiagnosticWarning,
    Note = c.MlirDiagnosticSeverity.MlirDiagnosticNote,
    Remark = c.MlirDiagnosticSeverity.MlirDiagnosticRemark,
};

/// =============================
/// Diagnostic Struct
/// =============================
/// Diagnostic encapsulates the MlirDiagnostic struct.
pub const Diagnostic = struct {
    handle: c.MlirDiagnostic,

    /// Prints the diagnostic using the provided callback.
    // pub fn print(self: Diagnostic, callback: fn ([]const u8) void, userData: anytype) void {
    //     // Define a C callback that bridges to the Zig callback.
    //     extern "c" fn c_callback(s: * u8, len: usize, userData: *c_void) void {
    //         // Cast userData back to the Zig callback.
    //         const cb = @ptrCast(fn ([]const u8) void, userData);
    //         cb(std.mem.sliceConst(u8, s, len));
    //     }
    //
    //     c.mlirDiagnosticPrint(
    //         self.handle,
    //         c.MlirStringCallback(c_callback),
    //         @ptrCast(void *, callback),
    //     );
    // }

    /// Retrieves the location of the diagnostic.
    pub fn getLocation(self: Diagnostic) Type.Location {
        return Type.Location{ .handle = c.mlirDiagnosticGetLocation(self.handle) };
    }

    /// Retrieves the severity of the diagnostic.
    pub fn getSeverity(self: Diagnostic) DiagnosticSeverity {
        return switch (c.mlirDiagnosticGetSeverity(self.handle)) {
            c.MlirDiagnosticSeverity.MlirDiagnosticError => .Error,
            c.MlirDiagnosticSeverity.MlirDiagnosticWarning => .Warning,
            c.MlirDiagnosticSeverity.MlirDiagnosticNote => .Note,
            c.MlirDiagnosticSeverity.MlirDiagnosticRemark => .Remark,
            else => @panic("Unknown DiagnosticSeverity"),
        };
    }

    /// Retrieves the number of notes attached to the diagnostic.
    pub fn getNumNotes(self: Diagnostic) usize {
        return @intCast(c.mlirDiagnosticGetNumNotes(self.handle));
    }

    /// Retrieves the pos-th note attached to the diagnostic.
    pub fn getNote(self: Diagnostic, pos: usize) Diagnostic {
        return Diagnostic{ .handle = c.mlirDiagnosticGetNote(self.handle, @intCast(pos)) };
    }
};

/// =============================
/// Diagnostic Handler
/// =============================
/// Opaque identifier for a diagnostic handler.
pub const DiagnosticHandlerID = u64;

/// Diagnostic handler function type.
pub const DiagnosticHandlerFn = fn (Diagnostic, anytype) c.MlirLogicalResult;
/// Detaches a diagnostic handler from the context using its identifier.
pub fn detachDiagnosticHandler(self: Context, id: DiagnosticHandlerID) void {
    c.mlirContextDetachDiagnosticHandler(self.handle, id);
}

/// Emits an error at the given location through the diagnostics engine.
pub fn emitError(location: Location, message: []const u8) void {
    c.mlirEmitError(location.handle, @ptrCast(message));
}

/// Callback type for printing.
pub const StringCallback = fn ([]const u8, anyopaque) callconv(.c) void;

//-------------------------------------
// AffineExpr
//-------------------------------------
pub const AffineExpr = struct {
    handle: c.MlirAffineExpr,

    /// Gets the context that owns the affine expression.
    pub fn getContext(self: AffineExpr) Context {
        return Context{ .handle = c.mlirAffineExprGetContext(self.handle) };
    }

    /// Checks whether the affine expression is null.
    pub fn isNull(self: AffineExpr) bool {
        return c.mlirAffineExprIsNull(self.handle);
    }

    /// Checks if two affine expressions are equal.
    pub fn equal(self: AffineExpr, other: AffineExpr) bool {
        return c.mlirAffineExprEqual(self.handle, other.handle);
    }

    /// Prints the affine expression by sending chunks of the string representation
    /// and forwarding `userData` to `callback`.
    pub fn print(self: AffineExpr, callback: StringCallback, userData: anyopaque) void {
        c.mlirAffineExprPrint(self.handle, callback, userData);
    }

    /// Dumps the affine expression to the standard error stream (useful for debugging).
    pub fn dump(self: AffineExpr) void {
        c.mlirAffineExprDump(self.handle);
    }

    /// Checks whether the affine expression is made out of only symbols and constants.
    pub fn isSymbolicOrConstant(self: AffineExpr) bool {
        return c.mlirAffineExprIsSymbolicOrConstant(self.handle);
    }

    /// Checks whether the affine expression is a pure affine expression,
    /// i.e., mul, floordiv, ceildic, and mod are only allowed with respect to constants.
    pub fn isPureAffine(self: AffineExpr) bool {
        return c.mlirAffineExprIsPureAffine(self.handle);
    }

    /// Returns the greatest known integral divisor of this affine expression.
    /// The result is always positive.
    pub fn getLargestKnownDivisor(self: AffineExpr) i64 {
        return c.mlirAffineExprGetLargestKnownDivisor(self.handle);
    }

    /// Checks whether the affine expression is a multiple of `factor`.
    pub fn isMultipleOf(self: AffineExpr, factor: i64) bool {
        return c.mlirAffineExprIsMultipleOf(self.handle, factor);
    }

    /// Checks whether the affine expression involves AffineDimExpr `position`.
    pub fn isFunctionOfDim(self: AffineExpr, position: isize) bool {
        return c.mlirAffineExprIsFunctionOfDim(self.handle, position);
    }

    /// Composes the given map with the given expression.
    pub fn compose(self: AffineExpr, map: AffineMap) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineExprCompose(self.handle, map.handle),
        };
    }

    /// Checks whether the affine expression is a dimension expression.
    pub fn isADim(self: AffineExpr) bool {
        return c.mlirAffineExprIsADim(self.handle);
    }

    /// Creates an affine dimension expression with `position` in the context.
    pub fn dimExprGet(ctx: Context, position: isize) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineDimExprGet(ctx.handle, position),
        };
    }

    /// Returns the position of the affine dimension expression.
    pub fn getDimPosition(self: AffineExpr) isize {
        return c.mlirAffineDimExprGetPosition(self.handle);
    }

    /// Checks whether the affine expression is a symbol expression.
    pub fn isASymbol(self: AffineExpr) bool {
        return c.mlirAffineExprIsASymbol(self.handle);
    }

    /// Creates an affine symbol expression with `position` in the context.
    pub fn symbolExprGet(ctx: Context, position: isize) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineSymbolExprGet(ctx.handle, position),
        };
    }

    /// Returns the position of the affine symbol expression.
    pub fn getSymbolPosition(self: AffineExpr) isize {
        return c.mlirAffineSymbolExprGetPosition(self.handle);
    }

    /// Checks whether the affine expression is a constant expression.
    pub fn isAConstant(self: AffineExpr) bool {
        return c.mlirAffineExprIsAConstant(self.handle);
    }

    /// Creates an affine constant expression with `constant` in the context.
    pub fn constantExprGet(ctx: Context, constant: i64) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineConstantExprGet(ctx.handle, constant),
        };
    }

    /// Returns the value of the affine constant expression.
    pub fn getConstantValue(self: AffineExpr) i64 {
        return c.mlirAffineConstantExprGetValue(self.handle);
    }

    /// Checks whether the affine expression is an add expression.
    pub fn isAAdd(self: AffineExpr) bool {
        return c.mlirAffineExprIsAAdd(self.handle);
    }

    /// Creates an affine add expression with `lhs` and `rhs`.
    pub fn addExprGet(lhs: AffineExpr, rhs: AffineExpr) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineAddExprGet(lhs.handle, rhs.handle),
        };
    }

    /// Checks whether the affine expression is a mul expression.
    pub fn isAMul(self: AffineExpr) bool {
        return c.mlirAffineExprIsAMul(self.handle);
    }

    /// Creates an affine mul expression with `lhs` and `rhs`.
    pub fn mulExprGet(lhs: AffineExpr, rhs: AffineExpr) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineMulExprGet(lhs.handle, rhs.handle),
        };
    }

    /// Checks whether the affine expression is a mod expression.
    pub fn isAMod(self: AffineExpr) bool {
        return c.mlirAffineExprIsAMod(self.handle);
    }

    /// Creates an affine mod expression with `lhs` and `rhs`.
    pub fn modExprGet(lhs: AffineExpr, rhs: AffineExpr) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineModExprGet(lhs.handle, rhs.handle),
        };
    }

    /// Checks whether the affine expression is a floor division expression.
    pub fn isAFloorDiv(self: AffineExpr) bool {
        return c.mlirAffineExprIsAFloorDiv(self.handle);
    }

    /// Creates an affine floor division expression with `lhs` and `rhs`.
    pub fn floorDivExprGet(lhs: AffineExpr, rhs: AffineExpr) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineFloorDivExprGet(lhs.handle, rhs.handle),
        };
    }

    /// Checks whether the affine expression is a ceil division expression.
    pub fn isACeilDiv(self: AffineExpr) bool {
        return c.mlirAffineExprIsACeilDiv(self.handle);
    }

    /// Creates an affine ceil division expression with `lhs` and `rhs`.
    pub fn ceilDivExprGet(lhs: AffineExpr, rhs: AffineExpr) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineCeilDivExprGet(lhs.handle, rhs.handle),
        };
    }

    /// Checks whether the affine expression is a binary operation expression.
    pub fn isABinary(self: AffineExpr) bool {
        return c.mlirAffineExprIsABinary(self.handle);
    }

    /// Returns the left-hand side of the binary operation expression.
    pub fn getBinaryLHS(self: AffineExpr) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineBinaryOpExprGetLHS(self.handle),
        };
    }

    /// Returns the right-hand side of the binary operation expression.
    pub fn getBinaryRHS(self: AffineExpr) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineBinaryOpExprGetRHS(self.handle),
        };
    }
};

//-------------------------------------
// AffineMap
//-------------------------------------
pub const AffineMap = struct {
    handle: c.MlirAffineMap,

    /// Gets the context that the affine map was created with.
    pub fn getContext(self: AffineMap) Context {
        return Context{ .handle = c.mlirAffineMapGetContext(self.handle) };
    }

    /// Checks whether the affine map is null.
    pub fn isNull(self: AffineMap) bool {
        return c.mlirAffineMapIsNull(self.handle);
    }

    /// Checks if two affine maps are equal.
    pub fn equal(self: AffineMap, other: AffineMap) bool {
        return c.mlirAffineMapEqual(self.handle, other.handle);
    }

    /// Prints the affine map by sending chunks of the string representation
    /// and forwarding `userData` to `callback`.
    pub fn print(self: AffineMap, callback: StringCallback, userData: anyopaque) void {
        c.mlirAffineMapPrint(self.handle, callback, userData);
    }

    /// Dumps the affine map to the standard error stream (useful for debugging).
    pub fn dump(self: AffineMap) void {
        c.mlirAffineMapDump(self.handle);
    }

    /// Creates an empty affine map with zero results, no dimensions, and no symbols.
    pub fn emptyGet(ctx: Context) AffineMap {
        return AffineMap{ .handle = c.mlirAffineMapEmptyGet(ctx.handle) };
    }

    /// Creates a zero-result affine map with the given number of dimensions and symbols.
    pub fn zeroResultGet(ctx: Context, dimCount: isize, symbolCount: isize) AffineMap {
        return AffineMap{
            .handle = c.mlirAffineMapZeroResultGet(ctx.handle, dimCount, symbolCount),
        };
    }

    /// Creates an affine map with the specified dimensions, symbols, and affine expressions.
    pub fn get(ctx: Context, dimCount: isize, symbolCount: isize, affineExprs: []const AffineExpr) AffineMap {
        var exprArray = SmallVector(c.MlirAffineExpr, 8).init(global_alloc);
        defer exprArray.deinit();
        for (affineExprs) |expr| {
            exprArray.push(expr.handle);
        }

        return AffineMap{
            .handle = c.mlirAffineMapGet(ctx.handle, dimCount, symbolCount, @intCast(affineExprs.len), exprArray.ptr),
        };
    }

    /// Creates a constant affine map with a single result.
    pub fn constantGet(ctx: Context, val: i64) AffineMap {
        return AffineMap{
            .handle = c.mlirAffineMapConstantGet(ctx.handle, val),
        };
    }

    /// Creates a multi-dimensional identity affine map.
    pub fn multiDimIdentityGet(ctx: Context, numDims: isize) AffineMap {
        return AffineMap{
            .handle = c.mlirAffineMapMultiDimIdentityGet(ctx.handle, numDims),
        };
    }

    /// Creates a minor identity affine map.
    pub fn minorIdentityGet(ctx: Context, dims: isize, results: isize) AffineMap {
        return AffineMap{
            .handle = c.mlirAffineMapMinorIdentityGet(ctx.handle, dims, results),
        };
    }

    /// Creates a permutation affine map.
    pub fn permutationGet(ctx: Context, size: isize, permutation: []const u32) AffineMap {
        var permArray = SmallVector(u32, 8).init(global_alloc);
        defer permArray.deinit();
        for (permutation) |val| {
            permArray.push(val);
        }

        return AffineMap{
            .handle = c.mlirAffineMapPermutationGet(
                ctx.handle,
                size,
                permArray.ptr,
            ),
        };
    }

    /// Checks if the affine map is an identity map.
    pub fn isIdentity(self: AffineMap) bool {
        return c.mlirAffineMapIsIdentity(self.handle);
    }

    /// Checks if the affine map is a minor identity map.
    pub fn isMinorIdentity(self: AffineMap) bool {
        return c.mlirAffineMapIsMinorIdentity(self.handle);
    }

    /// Checks if the affine map is empty.
    pub fn isEmpty(self: AffineMap) bool {
        return c.mlirAffineMapIsEmpty(self.handle);
    }

    /// Checks if the affine map is a single constant map.
    pub fn isSingleConstant(self: AffineMap) bool {
        return c.mlirAffineMapIsSingleConstant(self.handle);
    }

    /// Gets the single constant result of the affine map.
    /// Asserts that the map has exactly one constant result.
    pub fn getSingleConstantResult(self: AffineMap) i64 {
        return c.mlirAffineMapGetSingleConstantResult(self.handle);
    }

    /// Gets the number of dimensions in the affine map.
    pub fn getNumDims(self: AffineMap) usize {
        return @intCast(c.mlirAffineMapGetNumDims(self.handle));
    }

    /// Gets the number of symbols in the affine map.
    pub fn getNumSymbols(self: AffineMap) usize {
        return @intCast(c.mlirAffineMapGetNumSymbols(self.handle));
    }

    /// Gets the number of results in the affine map.
    pub fn getNumResults(self: AffineMap) usize {
        return @intCast(c.mlirAffineMapGetNumResults(self.handle));
    }

    /// Gets the affine expression result at the specified position.
    pub fn getResult(self: AffineMap, pos: usize) AffineExpr {
        return AffineExpr{
            .handle = c.mlirAffineMapGetResult(self.handle, @intCast(pos)),
        };
    }

    /// Gets the number of inputs (dimensions + symbols) in the affine map.
    pub fn getNumInputs(self: AffineMap) usize {
        return @intCast(c.mlirAffineMapGetNumInputs(self.handle));
    }

    /// Checks if the affine map is a projected permutation.
    pub fn isProjectedPermutation(self: AffineMap) bool {
        return c.mlirAffineMapIsProjectedPermutation(self.handle);
    }

    /// Checks if the affine map is a permutation map.
    pub fn isPermutation(self: AffineMap) bool {
        return c.mlirAffineMapIsPermutation(self.handle);
    }

    /// Gets a submap based on the provided result positions.
    pub fn getSubMap(self: AffineMap, resultPos: []const isize) AffineMap {
        var posArray = SmallVector(isize, 8).init(global_alloc);
        defer posArray.deinit();
        for (resultPos) |pos| {
            posArray.push(pos);
        }

        return AffineMap{
            .handle = c.mlirAffineMapGetSubMap(
                self.handle,
                @intCast(resultPos.len),
                posArray.ptr,
            ),
        };
    }

    /// Gets a major submap consisting of the most major `numResults` results.
    pub fn getMajorSubMap(self: AffineMap, numResults: isize) AffineMap {
        return AffineMap{
            .handle = c.mlirAffineMapGetMajorSubMap(self.handle, numResults),
        };
    }

    /// Gets a minor submap consisting of the most minor `numResults` results.
    pub fn getMinorSubMap(self: AffineMap, numResults: isize) AffineMap {
        return AffineMap{
            .handle = c.mlirAffineMapGetMinorSubMap(self.handle, numResults),
        };
    }

    /// Replaces affine expressions within the map and returns a new affine map.
    pub fn replace(self: AffineMap, expression: AffineExpr, replacement: AffineExpr, numResultDims: isize, numResultSyms: isize) AffineMap {
        return AffineMap{
            .handle = c.mlirAffineMapReplace(
                self.handle,
                expression.handle,
                replacement.handle,
                numResultDims,
                numResultSyms,
            ),
        };
    }
};

//-------------------------------------
// IntegerSet
//-------------------------------------
pub const IntegerSet = struct {
    handle: c.MlirIntegerSet,

    /// Gets the context in which the integer set lives.
    pub fn getContext(self: IntegerSet) Context {
        return Context{ .handle = c.mlirIntegerSetGetContext(self.handle) };
    }

    /// Checks whether the integer set is null.
    pub fn isNull(self: IntegerSet) bool {
        return c.mlirIntegerSetIsNull(self.handle);
    }

    /// Checks if two integer sets are equal.
    ///
    /// **Note:** This is a shallow comparison. For deep equivalence, use set difference and emptiness checks.
    pub fn equal(self: IntegerSet, other: IntegerSet) bool {
        return c.mlirIntegerSetEqual(self.handle, other.handle);
    }

    /// Prints the integer set by sending chunks of the string representation
    /// and forwarding `userData` to `callback`.
    pub fn print(self: IntegerSet, callback: StringCallback, userData: anyopaque) void {
        c.mlirIntegerSetPrint(self.handle, callback, userData);
    }

    /// Dumps the integer set to the standard error stream (useful for debugging).
    pub fn dump(self: IntegerSet) void {
        c.mlirIntegerSetDump(self.handle);
    }

    /// Gets or creates a new canonically empty integer set with the given number of
    /// dimensions and symbols in the given context.
    pub fn emptyGet(ctx: Context, numDims: isize, numSymbols: isize) IntegerSet {
        return IntegerSet{ .handle = c.mlirIntegerSetEmptyGet(ctx.handle, numDims, numSymbols) };
    }

    /// Gets or creates a new integer set in the given context. The set is defined
    /// by a list of affine constraints, with the given number of input dimensions
    /// and symbols, which are treated as either equalities (`eqFlags` is `true`)
    /// or inequalities (`eqFlags` is `false`). Both `constraints` and `eqFlags` are
    /// expected to point to at least `numConstraints` consecutive values.
    pub fn get(
        ctx: Context,
        numDims: isize,
        numSymbols: isize,
        constraints: []const AffineExpr,
        eqFlags: []const bool,
    ) IntegerSet {
        // Ensure that the lengths of constraints and eqFlags match.
        std.debug.assert(constraints.len == eqFlags.len);

        // Allocate memory for C affine expressions and equality flags.
        var allocator = global_alloc;
        var exprArray = allocator.alloc(c.MlirAffineExpr, constraints.len) catch {
            std.debug.print("Failed to allocate memory for constraints.\n", .{});
            return IntegerSet{ .handle = undefined };
        };
        defer allocator.free(exprArray);

        var flagsArray = allocator.alloc(c.bool, eqFlags.len) catch {
            std.debug.print("Failed to allocate memory for equality flags.\n", .{});
            return IntegerSet{ .handle = undefined };
        };
        defer allocator.free(flagsArray);

        // Populate the C affine expressions and equality flags arrays.
        for (constraints, 0..) |expr, idx| {
            exprArray[idx] = expr.handle;
        }

        for (eqFlags, 0..) |flag, idx| {
            flagsArray[idx] = flag;
        }

        return IntegerSet{
            .handle = c.mlirIntegerSetGet(
                ctx.handle,
                numDims,
                numSymbols,
                @intCast(constraints.len),
                exprArray.ptr,
                flagsArray.ptr,
            ),
        };
    }

    /// Gets or creates a new integer set in which the values and dimensions of the
    /// given set are replaced with the given affine expressions. `dimReplacements`
    /// and `symbolReplacements` are expected to point to at least as many
    /// consecutive expressions as the given set has dimensions and symbols,
    /// respectively. The new set will have `numResultDims` and `numResultSymbols`
    /// dimensions and symbols, respectively.
    pub fn replaceGet(
        set: IntegerSet,
        dimReplacements: []const AffineExpr,
        symbolReplacements: []const AffineExpr,
        numResultDims: isize,
        numResultSymbols: isize,
    ) IntegerSet {
        // Allocate memory for dimension replacements.

        var dimArray = SmallVector(c.MlirAffineExpr, 8).init(global_alloc);
        defer dimArray.deinit();
        for (dimReplacements) |expr| {
            dimArray.push(expr.handle);
        }

        var symArray = SmallVector(c.MlirAffineExpr, 8).init(global_alloc);
        defer symArray.deinit();
        for (symbolReplacements) |expr| {
            symArray.push(expr.handle);
        }

        return IntegerSet{
            .handle = c.mlirIntegerSetReplaceGet(
                set.handle,
                dimArray.ptr,
                symArray.ptr,
                numResultDims,
                numResultSymbols,
            ),
        };
    }

    /// Checks whether the given set is a canonical empty set, e.g., the set
    /// returned by `emptyGet`.
    pub fn isCanonicalEmpty(self: IntegerSet) bool {
        return c.mlirIntegerSetIsCanonicalEmpty(self.handle);
    }

    /// Returns the number of dimensions in the given set.
    pub fn getNumDims(self: IntegerSet) usize {
        return @intCast(c.mlirIntegerSetGetNumDims(self.handle));
    }

    /// Returns the number of symbols in the given set.
    pub fn getNumSymbols(self: IntegerSet) usize {
        return @intCast(c.mlirIntegerSetGetNumSymbols(self.handle));
    }

    /// Returns the number of inputs (dimensions + symbols) in the given set.
    pub fn getNumInputs(self: IntegerSet) usize {
        return @intCast(c.mlirIntegerSetGetNumInputs(self.handle));
    }

    /// Returns the number of constraints (equalities + inequalities) in the given set.
    pub fn getNumConstraints(self: IntegerSet) usize {
        return @intCast(c.mlirIntegerSetGetNumConstraints(self.handle));
    }

    /// Returns the number of equalities in the given set.
    pub fn getNumEqualities(self: IntegerSet) usize {
        return @intCast(c.mlirIntegerSetGetNumEqualities(self.handle));
    }

    /// Returns the number of inequalities in the given set.
    pub fn getNumInequalities(self: IntegerSet) usize {
        return @intCast(c.mlirIntegerSetGetNumInequalities(self.handle));
    }

    /// Returns the `pos`-th constraint of the set.
    pub fn getConstraint(self: IntegerSet, pos: usize) AffineExpr {
        return AffineExpr{
            .handle = c.mlirIntegerSetGetConstraint(self.handle, @intCast(pos)),
        };
    }

    /// Returns `true` if the `pos`-th constraint of the set is an equality
    /// constraint, `false` otherwise.
    pub fn isConstraintEq(self: IntegerSet, pos: usize) bool {
        return c.mlirIntegerSetIsConstraintEq(self.handle, @intCast(pos));
    }
};

// =============================
// Enums
// =============================

/// MlirLLVMCConv corresponds to the C enum MlirLLVMCConv.
pub const LLVMCConv = enum(c_uint) {
    C = 0,
    Fast = 8,
    Cold = 9,
    GHC = 10,
    HiPE = 11,
    AnyReg = 13,
    PreserveMost = 14,
    PreserveAll = 15,
    Swift = 16,
    CXX_FAST_TLS = 17,
    Tail = 18,
    CFGuard_Check = 19,
    SwiftTail = 20,
    X86_StdCall = 64,
    X86_FastCall = 65,
    ARM_APCS = 66,
    ARM_AAPCS = 67,
    ARM_AAPCS_VFP = 68,
    MSP430_INTR = 69,
    X86_ThisCall = 70,
    PTX_Kernel = 71,
    PTX_Device = 72,
    SPIR_FUNC = 75,
    SPIR_KERNEL = 76,
    Intel_OCL_BI = 77,
    X86_64_SysV = 78,
    Win64 = 79,
    X86_VectorCall = 80,
    DUMMY_HHVM = 81,
    DUMMY_HHVM_C = 82,
    X86_INTR = 83,
    AVR_INTR = 84,
    AVR_BUILTIN = 86,
    AMDGPU_VS = 87,
    AMDGPU_GS = 88,
    AMDGPU_CS = 90,
    AMDGPU_KERNEL = 91,
    X86_RegCall = 92,
    AMDGPU_HS = 93,
    MSP430_BUILTIN = 94,
    AMDGPU_LS = 95,
    AMDGPU_ES = 96,
    AArch64_VectorCall = 97,
    AArch64_SVE_VectorCall = 98,
    WASM_EmscriptenInvoke = 99,
    AMDGPU_Gfx = 100,
    M68k_INTR = 101,
};

/// MlirLLVMComdat corresponds to the C enum MlirLLVMComdat.
pub const LLVMComdat = enum(c_int) {
    Any = 0,
    ExactMatch = 1,
    Largest = 2,
    NoDeduplicate = 3,
    SameSize = 4,
};

/// MlirLLVMLinkage corresponds to the C enum MlirLLVMLinkage.
pub const LLVMLinkage = enum(c_int) {
    External,
    AvailableExternally,
    Linkonce,
    LinkonceODR,
    Weak,
    WeakODR,
    Appending,
    Internal,
    Private,
    ExternWeak,
    Common,
};

/// MlirLLVMTypeEncoding corresponds to the C enum MlirLLVMTypeEncoding.
pub const LLVMTypeEncoding = enum(u8) {
    Address = 0x1,
    Boolean = 0x2,
    ComplexFloat = 0x31,
    FloatT = 0x4,
    Signed = 0x5,
    SignedChar = 0x6,
    Unsigned = 0x7,
    UnsignedChar = 0x08,
    ImaginaryFloat = 0x09,
    PackedDecimal = 0x0a,
    NumericString = 0x0b,
    Edited = 0x0c,
    SignedFixed = 0x0d,
    UnsignedFixed = 0x0e,
    DecimalFloat = 0x0f,
    UTF = 0x10,
    UCS = 0x11,
    ASCII = 0x12,
    LoUser = 0x80,
    HiUser = 0xff,
};

/// MlirLLVMDIEmissionKind corresponds to the C enum MlirLLVMDIEmissionKind.
pub const LLVMDIEmissionKind = enum(c_int) {
    None = 0,
    Full = 1,
    LineTablesOnly = 2,
    DebugDirectivesOnly = 3,
};

/// MlirLLVMDINameTableKind corresponds to the C enum MlirLLVMDINameTableKind.
pub const LLVMDINameTableKind = enum(c_int) {
    Default = 0,
    GNU = 1,
    None = 2,
    Apple = 3,
};

// =============================
// LLVM Type Wrappers
// =============================

/// Type wrapper extension for LLVM types.
pub const LLVM = struct {
    /// Creates an llvm.ptr type.
    pub fn getPointerType(ctx: Context, addressSpace: u32) Type {
        const llvmPtrType = c.mlirLLVMPointerTypeGet(ctx.handle, @intCast(addressSpace));
        return Type{ .handle = llvmPtrType };
    }

    /// Returns `true` if the type is an LLVM dialect pointer type.
    pub fn isLLVMPointerType(type_: Type) bool {
        return c.mlirTypeIsALLVMPointerType(type_.handle);
    }

    /// Returns address space of llvm.ptr
    pub fn getLLVMPointerTypeAddressSpace(type_: Type) u32 {
        return @intCast(c.mlirLLVMPointerTypeGetAddressSpace(type_.handle));
    }

    /// Creates an llvm.void type.
    pub fn getLLVMVoidType(ctx: Context) Type {
        const llvmVoidType = c.mlirLLVMVoidTypeGet(ctx.handle);
        return Type{ .handle = llvmVoidType };
    }

    /// Creates an llvm.array type.
    pub fn getLLVMArrayType(elementType: Type, numElements: u32) Type {
        const llvmArrayType = c.mlirLLVMArrayTypeGet(elementType.handle, @intCast(numElements));
        return Type{ .handle = llvmArrayType };
    }

    /// Creates an llvm.func type.
    pub fn getLLVMFunctionType(
        resultType: Type,
        argumentTypes: []const Type,
        isVarArg: bool,
    ) Type {
        return Type{
            .handle = c.mlirLLVMFunctionTypeGet(
                resultType.handle,
                @intCast(argumentTypes.len),
                @ptrCast(argumentTypes.ptr),
                isVarArg,
            ),
        };
    }

    /// Returns `true` if the type is an LLVM dialect struct type.
    pub fn isLLVMStructType(type_: Type) bool {
        return c.mlirTypeIsALLVMStructType(type_.handle);
    }

    /// Returns `true` if the type is a literal (unnamed) LLVM struct type.
    pub fn isLLVMStructTypeLiteral(type_: Type) bool {
        return c.mlirLLVMStructTypeIsLiteral(type_.handle);
    }

    /// Returns the number of fields in the struct. Asserts if the struct is opaque or not yet initialized.
    pub fn getLLVMStructTypeNumElementTypes(type_: Type) usize {
        return @intCast(c.mlirLLVMStructTypeGetNumElementTypes(type_.handle));
    }

    /// Returns the `position`-th field of the struct. Asserts if the struct is opaque, not yet initialized or if the position is out of range.
    pub fn getLLVMStructTypeElementType(type_: Type, position: usize) Type {
        return Type{
            .handle = c.mlirLLVMStructTypeGetElementType(type_.handle, @intCast(position)),
        };
    }

    /// Returns `true` if the struct is packed.
    pub fn isLLVMStructTypePacked(type_: Type) bool {
        return c.mlirLLVMStructTypeIsPacked(type_.handle);
    }

    /// Returns the identifier of the identified struct. Asserts that the struct is identified, i.e., not literal.
    pub fn getLLVMStructTypeIdentifier(type_: Type) StringRef {
        return StringRef{ .inner = c.mlirLLVMStructTypeGetIdentifier(type_.handle) };
    }

    /// Returns `true` if the struct is explicitly opaque (will not have a body) or uninitialized (will eventually have a body).
    pub fn isLLVMStructTypeOpaque(type_: Type) bool {
        return c.mlirLLVMStructTypeIsOpaque(type_.handle);
    }

    /// Creates an LLVM literal (unnamed) struct type. This may assert if the fields have types not compatible with the LLVM dialect. For a graceful failure, use the checked version.
    pub fn getLLVMStructTypeLiteral(ctx: Context, fieldTypes: []const Type, isPacked: bool) Type {
        return Type{
            .handle = c.mlirLLVMStructTypeLiteralGet(
                ctx.handle,
                @intCast(fieldTypes.len),
                @ptrCast(fieldTypes.ptr),
                isPacked,
            ),
        };
    }

    /// Creates an LLVM literal (unnamed) struct type if possible. Emits a diagnostic at the given location and returns null otherwise.
    pub fn getLLVMStructTypeLiteralChecked(
        loc: Type.Location,
        fieldTypes: []const Type,
        isPacked: bool,
    ) ?Type {
        const llvmStructType = c.mlirLLVMStructTypeLiteralGetChecked(
            loc.handle,
            @intCast(fieldTypes.len),
            @ptrCast(fieldTypes.ptr),
            @intCast(isPacked),
        );
        if (llvmStructType.ptr == null) return null;
        return Type{ .handle = llvmStructType };
    }

    /// Creates an LLVM identified struct type with no body. If a struct type with this name already exists in the context, returns that type. Use mlirLLVMStructTypeIdentifiedNewGet to create a fresh struct type, potentially renaming it. The body should be set separately by calling mlirLLVMStructTypeSetBody, if it isn't set already.
    pub fn getLLVMStructTypeIdentified(ctx: Context, name: StringRef) Type {
        const llvmStructType = c.mlirLLVMStructTypeIdentifiedGet(ctx.handle, name.inner);
        return Type{ .handle = llvmStructType };
    }

    /// Creates an LLVM identified struct type with no body and a name starting with the given prefix. If a struct with the exact name as the given prefix already exists, appends an unspecified suffix to the name so that the name is unique in context.
    pub fn getLLVMStructTypeIdentifiedNew(
        ctx: Context,
        name: StringRef,
        fieldTypes: []const Type,
        isPacked: bool,
    ) Type {
        return Type{
            .handle = c.mlirLLVMStructTypeIdentifiedNewGet(
                ctx.handle,
                name.inner,
                @intCast(fieldTypes.len),
                @ptrCast(fieldTypes.ptr),
                @intCast(isPacked),
            ),
        };
    }

    /// Creates an LLVM opaque struct type with the given name.
    pub fn getLLVMStructTypeOpaque(ctx: Context, name: StringRef) Type {
        const llvmStructType = c.mlirLLVMStructTypeOpaqueGet(ctx.handle, name.inner);
        return Type{ .handle = llvmStructType };
    }

    /// Sets the body of the identified struct if it hasn't been set yet. Returns whether the operation was successful.
    pub fn setLLVMStructTypeBody(
        type_: Type,
        fieldTypes: []const Type,
        isPacked: bool,
    ) LogicalResult {
        return LogicalResult{
            .handle = c.mlirLLVMStructTypeSetBody(
                type_.handle,
                @intCast(fieldTypes.len),
                @ptrCast(fieldTypes.ptr),
                @intCast(isPacked),
            ),
        };
    }
};

// =============================
// LLVM Attribute Wrappers
// =============================

/// Attribute wrapper extension for LLVM attributes.
pub const LLVMAttributes = struct {
    /// Creates a LLVM CConv attribute.
    pub fn getLLVMCConvAttr(ctx: Context, cconv: LLVMCConv) Attribute {
        const attr = c.mlirLLVMCConvAttrGet(ctx.handle, @intFromEnum(cconv));
        return Attribute{ .handle = attr };
    }

    /// Creates a LLVM Comdat attribute.
    pub fn getLLVMComdatAttr(ctx: Context, comdat: LLVMComdat) Attribute {
        const attr = c.mlirLLVMComdatAttrGet(ctx.handle, @intCast(comdat));
        return Attribute{ .handle = attr };
    }

    /// Creates a LLVM Linkage attribute.
    pub fn getLLVMLinkageAttr(ctx: Context, linkage: LLVMLinkage) Attribute {
        const attr = c.mlirLLVMLinkageAttrGet(ctx.handle, @intCast(@intFromEnum(linkage)));
        return Attribute{ .handle = attr };
    }

    /// Creates a LLVM DINullType attribute.
    pub fn getLLVMDINullTypeAttr(ctx: Context) Attribute {
        const attr = c.mlirLLVMDINullTypeAttrGet(ctx.handle);
        return Attribute{ .handle = attr };
    }

    /// Creates a LLVM DIExpressionElem attribute.
    pub fn getLLVMDIExpressionElemAttr(
        ctx: Context,
        opcode: u32,
        arguments: []const u64,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIExpressionElemAttrGet(
                ctx.handle,
                @intCast(opcode),
                @intCast(arguments.len),
                @ptrCast(arguments.ptr),
            ),
        };
    }

    /// Creates a LLVM DIExpression attribute.
    pub fn getLLVMDIExpressionAttr(
        ctx: Context,
        operations: []const Attribute,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIExpressionAttrGet(
                ctx.handle,
                @intCast(operations.len),
                @ptrCast(operations.ptr),
            ),
        };
    }

    /// Creates a LLVM DIBasicType attribute.
    pub fn getLLVMDIBasicTypeAttr(
        ctx: Context,
        tag: u32,
        name: Attribute,
        sizeInBits: u64,
        encoding: LLVMTypeEncoding,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIBasicTypeAttrGet(
                ctx.handle,
                @intCast(tag),
                name.handle,
                sizeInBits,
                @intFromEnum(encoding),
            ),
        };
    }

    /// Creates a self-referencing LLVM DICompositeType attribute.
    pub fn getLLVMDICompositeTypeAttrRecSelf(recId: Attribute) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDICompositeTypeAttrGetRecSelf(recId.handle),
        };
    }

    /// Creates a LLVM DICompositeType attribute.
    pub fn getLLVMDICompositeTypeAttr(
        ctx: Context,
        recId: Attribute,
        isRecSelf: bool,
        tag: u32,
        name: Attribute,
        file: Attribute,
        line: u32,
        scope: Attribute,
        baseType: Attribute,
        flags: i64,
        sizeInBits: u64,
        alignInBits: u64,
        elements: []const Type,
        dataLocation: Attribute,
        rank: Attribute,
        allocated: Attribute,
        associated: Attribute,
    ) LogicalResult {
        return LogicalResult{
            .handle = c.mlirLLVMDICompositeTypeAttrGet(
                ctx.handle,
                recId.handle,
                @intCast(isRecSelf),
                @intCast(tag),
                name.handle,
                file.handle,
                @intCast(line),
                scope.handle,
                baseType.handle,
                flags,
                sizeInBits,
                alignInBits,
                @intCast(elements.len),
                @ptrCast(elements.ptr),
                dataLocation.handle,
                rank.handle,
                allocated.handle,
                associated.handle,
            ),
        };
    }

    /// Creates a LLVM DIDerivedType attribute.
    pub fn getLLVMDIDerivedTypeAttr(
        ctx: Context,
        tag: u32,
        name: Attribute,
        baseType: Attribute,
        sizeInBits: u64,
        alignInBits: u32,
        offsetInBits: u64,
        dwarfAddressSpace: i64,
        extraData: Attribute,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIDerivedTypeAttrGet(
                ctx.handle,
                @intCast(tag),
                name.handle,
                baseType.handle,
                sizeInBits,
                alignInBits,
                offsetInBits,
                dwarfAddressSpace,
                extraData.handle,
            ),
        };
    }

    /// Creates a LLVM DIStringType attribute.
    pub fn getLLVMDIStringTypeAttr(
        ctx: Context,
        tag: u32,
        name: Attribute,
        sizeInBits: u64,
        alignInBits: u32,
        stringLength: Attribute,
        stringLengthExp: Attribute,
        stringLocationExp: Attribute,
        encoding: LLVMTypeEncoding,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIStringTypeAttrGet(
                ctx.handle,
                @intCast(tag),
                name.handle,
                sizeInBits,
                alignInBits,
                stringLength.handle,
                stringLengthExp.handle,
                stringLocationExp.handle,
                @intCast(encoding),
            ),
        };
    }

    /// Constant to represent std::nullopt for dwarfAddressSpace to omit the field.
    pub const DWARF_ADDRESS_SPACE_NULL = -1;

    /// Gets the base type from a LLVM DIDerivedType attribute.
    pub fn getLLVMDIDerivedTypeAttrBaseType(diDerivedType: Attribute) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIDerivedTypeAttrGetBaseType(diDerivedType.handle),
        };
    }

    /// Creates a LLVM DIFileAttr attribute.
    pub fn getLLVMDIFileAttr(
        ctx: Context,
        name: Attribute,
        directory: Attribute,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIFileAttrGet(ctx.handle, name.handle, directory.handle),
        };
    }

    /// Creates a LLVM DIAnnotation attribute.
    pub fn getLLVMDIAnnotationAttr(
        ctx: Context,
        name: Attribute,
        value: Attribute,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIAnnotationAttrGet(ctx.handle, name.handle, value.handle),
        };
    }

    /// Creates a LLVM DIModuleAttr attribute.
    pub fn getLLVMDIModuleAttr(
        ctx: Context,
        file: Attribute,
        scope: Attribute,
        name: Attribute,
        configMacros: Attribute,
        includePath: Attribute,
        apinotes: Attribute,
        line: u32,
        isDecl: bool,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIModuleAttrGet(
                ctx.handle,
                file.handle,
                scope.handle,
                name.handle,
                configMacros.handle,
                includePath.handle,
                apinotes.handle,
                @intCast(line),
                @intCast(isDecl),
            ),
        };
    }
    /// Gets the scope from this DISubprogramAttr.
    pub fn getLLVMDISubprogramAttrScope(diSubprogram: Attribute) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDISubprogramAttrGetScope(diSubprogram.handle),
        };
    }

    /// Gets the line from this DISubprogramAttr.
    pub fn getLLVMDISubprogramAttrLine(diSubprogram: Attribute) u32 {
        return @intCast(c.mlirLLVMDISubprogramAttrGetLine(diSubprogram.handle));
    }

    /// Gets the scope line from this DISubprogramAttr.
    pub fn getLLVMDISubprogramAttrScopeLine(diSubprogram: Attribute) u32 {
        return @intCast(c.mlirLLVMDISubprogramAttrGetScopeLine(diSubprogram.handle));
    }

    /// Gets the compile unit from this DISubprogramAttr.
    pub fn getLLVMDISubprogramAttrCompileUnit(diSubprogram: Attribute) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDISubprogramAttrGetCompileUnit(diSubprogram.handle),
        };
    }

    /// Gets the file from this DISubprogramAttr.
    pub fn getLLVMDISubprogramAttrFile(diSubprogram: Attribute) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDISubprogramAttrGetFile(diSubprogram.handle),
        };
    }

    /// Gets the type from this DISubprogramAttr.
    pub fn getLLVMDISubprogramAttrType(diSubprogram: Attribute) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDISubprogramAttrGetType(diSubprogram.handle),
        };
    }

    /// Creates a LLVM DISubroutineTypeAttr attribute.
    pub fn getLLVMDISubroutineTypeAttr(
        ctx: Context,
        callingConvention: u32,
        types: []const Attribute,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDISubroutineTypeAttrGet(
                ctx.handle,
                @intCast(callingConvention),
                @intCast(types.len),
                @ptrCast(types.ptr),
            ),
        };
    }

    /// Creates a LLVM DILexicalBlock attribute.
    pub fn getLLVMDILexicalBlockAttr(
        ctx: Context,
        scope: Attribute,
        file: Attribute,
        line: u32,
        column: u32,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDILexicalBlockAttrGet(
                ctx.handle,
                scope.handle,
                file.handle,
                @intCast(line),
                @intCast(column),
            ),
        };
    }

    /// Creates a LLVM DILexicalBlockFile attribute.
    pub fn getLLVMDILexicalBlockFileAttr(
        ctx: Context,
        scope: Attribute,
        file: Attribute,
        discriminator: u32,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDILexicalBlockFileAttrGet(
                ctx.handle,
                scope.handle,
                file.handle,
                @intCast(discriminator),
            ),
        };
    }

    /// Creates a LLVM DILocalVariableAttr attribute.
    pub fn getLLVMDILocalVariableAttr(
        ctx: Context,
        scope: Attribute,
        name: Attribute,
        diFile: Attribute,
        line: u32,
        arg: u32,
        alignInBits: u32,
        diType: Attribute,
        flags: i64,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDILocalVariableAttrGet(
                ctx.handle,
                scope.handle,
                name.handle,
                diFile.handle,
                @intCast(line),
                @intCast(arg),
                alignInBits,
                diType.handle,
                flags,
            ),
        };
    }

    /// Creates a LLVM DISubprogramAttr attribute.
    pub fn getLLVMDISubprogramAttr(
        ctx: Context,
        recId: Attribute,
        isRecSelf: bool,
        id: Attribute,
        compileUnit: Attribute,
        scope: Attribute,
        name: Attribute,
        linkageName: Attribute,
        file: Attribute,
        line: u32,
        scopeLine: u32,
        subprogramFlags: u64,
        type_: Attribute,
        retainedNodes: []const Attribute,
        annotations: []const Attribute,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDISubprogramAttrGet(
                ctx.handle,
                recId.handle,
                isRecSelf,
                id.handle,
                compileUnit.handle,
                scope.handle,
                name.handle,
                linkageName.handle,
                file.handle,
                @intCast(line),
                @intCast(scopeLine),
                subprogramFlags,
                type_.handle,
                @intCast(retainedNodes.len),
                @ptrCast(retainedNodes.ptr),
                @intCast(annotations.len),
                @ptrCast(annotations.ptr),
            ),
        };
    }

    /// Creates a LLVM DIImportedEntityAttr attribute.
    pub fn getLLVMDIImportedEntityAttr(
        ctx: Context,
        tag: u32,
        scope: Attribute,
        entity: Attribute,
        file: Attribute,
        line: u32,
        name: Attribute,
        elements: []const Attribute,
    ) Attribute {
        return Attribute{
            .handle = c.mlirLLVMDIImportedEntityAttrGet(
                ctx.handle,
                @intCast(tag),
                scope.handle,
                entity.handle,
                file.handle,
                @intCast(line),
                name.handle,
                @intCast(elements.len),
                @ptrCast(elements.ptr),
            ),
        };
    }
};

pub const DialectPluginLibraryInfo = extern struct {
    apiVersion: u32,
    pluginName: [*:0]const u8,
    pluginVersion: [*:0]const u8,
    registerDialectRegistryCallbacks: *const fn (c.MlirDialectRegistry) callconv(.c) void,
};
pub extern fn mlirGetDialectPluginInfo() DialectPluginLibraryInfo;
