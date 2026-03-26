module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // If reset stays low across sampled clocks, count is zero.
    check_reset_hold_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        !rst && !$past(rst) |-> (count == 4'h0)
    );

    // On the first sampled clock after reset, count is still zero.
    check_reset_release_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        rst && !$past(rst) |-> (count == 4'h0)
    );

    // With reset sampled high on consecutive clocks, count either increments or was asynchronously cleared.
    check_active_transition_increment_or_clear: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        $past(rst) |-> ((count == 4'h0) || (count == ($past(count) + 4'd1)))
    );

    // A previous maximum count wraps to zero on the next active sample.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        $past(rst) && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // Any nonzero active sample must match the previous count plus one.
    check_nonzero_active_count_increments: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
        $past(rst) && (count != 4'h0) |-> (count == ($past(count) + 4'd1))
    );

endmodule