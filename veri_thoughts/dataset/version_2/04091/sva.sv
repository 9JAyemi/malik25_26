module erosion_sys_cycle_time_sva (
    input logic        clock,
    input logic        resetn,
    input logic [31:0] cur_cycle
);

    // Counter output is zero whenever reset is asserted.
    check_reset_drives_zero: assert property (
        @(posedge clock) !resetn |-> (cur_cycle == 32'h0000_0000)
    );

    // First sampled cycle after reset release still shows zero.
    check_release_starts_from_zero: assert property (
        @(posedge clock) disable iff (!resetn)
        $rose(resetn) |-> (cur_cycle == 32'h0000_0000)
    );

    // One active clock after reset release, the counter becomes one.
    check_first_increment_after_release: assert property (
        @(posedge clock) disable iff (!resetn)
        $rose(resetn) |=> (cur_cycle == 32'h0000_0001)
    );

    // While continuously out of reset, the counter increments by one each cycle.
    check_increment_each_cycle: assert property (
        @(posedge clock) disable iff (!resetn)
        (!$initstate && $past(resetn)) |-> (cur_cycle == ($past(cur_cycle) + 32'h0000_0001))
    );

    // The 32-bit counter wraps to zero after reaching all ones.
    check_wraps_after_max: assert property (
        @(posedge clock) disable iff (!resetn)
        (!$initstate && $past(resetn) && ($past(cur_cycle) == 32'hFFFF_FFFF)) |-> (cur_cycle == 32'h0000_0000)
    );

endmodule