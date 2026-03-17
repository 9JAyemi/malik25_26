module up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A reset cycle forces count to zero on the next sampled clock.
    check_reset_forces_zero_next_cycle: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // The first non-reset cycle after reset still shows zero.
    check_count_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (count == 4'd0)
    );

    // Across consecutive non-reset cycles, count increments by one.
    check_count_increments_between_non_reset_cycles: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (count == ($past(count) + 4'd1))
    );

    // Across consecutive non-reset cycles, 4'hF wraps to 4'h0.
    check_count_wraps_from_f_to_0: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule