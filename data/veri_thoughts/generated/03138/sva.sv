module dffl_2_sva (
    input logic clk,
    input logic ld,
    input logic d,
    input logic reset,
    input logic q
);

    // Reset clears q on the following clock sample.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 1'b0)
    );

    // Reset takes priority over load when both are high.
    check_reset_priority_over_load: assert property (
        @(posedge clk) (reset && ld) |=> (q == 1'b0)
    );

    // When load is high and reset is low, q captures d.
    check_load_captures_d: assert property (
        @(posedge clk) disable iff (reset) ld |=> (q == $past(d))
    );

    // When load is low and reset is low, q holds its value.
    check_hold_when_load_low: assert property (
        @(posedge clk) disable iff (reset) !ld |=> (q == $past(q))
    );

endmodule