module counter_3bit_sync_reset_sva (
    input logic       clk,
    input logic       reset,
    input logic [2:0] count
);

    // Reset drives count to zero on the following cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'b000)
    );

    // If reset stays asserted, count remains zero.
    check_held_reset_keeps_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(reset) && reset) |-> (count == 3'b000)
    );

    // On the cycle after reset deasserts, count still reflects the reset value.
    check_reset_release_observes_zero: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset) |-> (count == 3'b000)
    );

    // In consecutive non-reset cycles, count increments by one.
    check_count_increments_without_reset: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (count == ($past(count) + 3'b001))
    );

    // The 3-bit counter wraps from 7 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && ($past(count) == 3'b111)) |-> (count == 3'b000)
    );

endmodule