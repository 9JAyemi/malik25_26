module up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A sampled low reset clears count by the next clock sample.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        !reset |=> (count == 4'h0)
    );

    // On the sampled cycle reset is released, count is still zero.
    check_count_zero_on_reset_release: assert property (
        @(posedge clk) disable iff ($initstate)
        $rose(reset) |-> (count == 4'h0)
    );

    // An active clock leads to either an incremented count or a zero if async reset intervenes.
    check_active_cycle_transition: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> ((count == 4'h0) || (count == ($past(count) + 4'd1)))
    );

    // From zero, the next sampled value is either one or zero if reset intervenes.
    check_zero_state_transition: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        (count == 4'h0) |=> ((count == 4'h0) || (count == 4'h1))
    );

    // From 4'hF, the next sampled value wraps to zero.
    check_max_state_wrap: assert property (
        @(posedge clk) disable iff (!reset || $initstate)
        (count == 4'hF) |=> (count == 4'h0)
    );

endmodule