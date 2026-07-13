module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        select,
    input logic [31:0] sum
);

    // Reset clears the registered output by the next clock.
    check_reset_clears_sum: assert property (
        @(posedge clk) reset |=> (sum == 32'h0000_0000)
    );

    // With select low, the output is the registered sum of a and b.
    check_select_low_sum: assert property (
        @(posedge clk) disable iff (reset)
        (!select) |=> (sum == $past(a + b))
    );

    // With select high, the output is the registered sum of a and ~b.
    check_select_high_sum: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (sum == $past(a + ~b))
    );

    // With select low, the output equals the previous cycle's a + b.
    check_select_low_sum_matches_prev_add: assert property (
        @(posedge clk) disable iff (reset)
        (!select) |=> (sum == $past(a + b))
    );

    // With select high, the output equals the previous cycle's a + ~b.
    check_select_high_sum_matches_prev_add: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (sum == $past(a + ~b))
    );

    // With select low, the output is the previous cycle's a + b.
    check_select_low_sum_matches_prev_add_no_pipeline: assert property (
        @(posedge clk) disable iff (reset)
        (!select) |=> (sum == $past(a + b))
    );

    // With select high, the output is the previous cycle's a + ~b.
    check_select_high_sum_matches_prev_add_no_pipeline: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (sum == $past(a + ~b))
    );

endmodule