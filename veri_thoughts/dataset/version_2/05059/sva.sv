module ldly1_5us_sva (
    input logic clk,
    input logic reset,
    input logic in,
    input logic p,
    input logic l,
    input logic [7:0] r
);

    // A sampled reset clears r and l.
    check_reset_clears_r_l: assert property (
        @(posedge clk) reset |=> (r == 8'd0 && l == 1'b0)
    );

    // An asserted input restarts the delay, raises l, and clears p.
    check_in_restarts_delay: assert property (
        @(posedge clk) disable iff (reset)
        in |=> (r == 8'd1 && l == 1'b1 && p == 1'b0)
    );

    // With no input, an asserted p clears r and l and stays asserted.
    check_p_branch_behavior: assert property (
        @(posedge clk) disable iff (reset)
        (!in && p) |=> (r == 8'd0 && l == 1'b0 && p == 1'b1)
    );

    // When the counter reaches 75 without input, p asserts and r holds.
    check_count_75_asserts_p: assert property (
        @(posedge clk) disable iff (reset)
        (!in && !p && (r == 8'd75)) |=> (p == 1'b1 && r == 8'd75)
    );

    // Before 75, the counter increments while l stays low and p stays low.
    check_counter_increments_before_75: assert property (
        @(posedge clk) disable iff (reset)
        (!in && !p && (r != 8'd75)) |=> (r == ($past(r) + 8'd1) && l == 1'b0 && p == 1'b0)
    );

endmodule