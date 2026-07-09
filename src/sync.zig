const std = @import("std");

pub const Mutex = struct {
    state: std.atomic.Value(bool) = std.atomic.Value(bool).init(false),

    pub fn lock(self: *Mutex) void {
        while (self.state.swap(true, .acquire) == true) {
            std.Thread.yield() catch {};
        }
    }

    pub fn unlock(self: *Mutex) void {
        self.state.store(false, .release);
    }

    pub fn tryLock(self: *Mutex) bool {
        return self.state.swap(true, .acquire) == false;
    }
};
