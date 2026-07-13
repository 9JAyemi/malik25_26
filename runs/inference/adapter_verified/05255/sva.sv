module binary_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [31:0] result
);

// Reset clears result on the next clock.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |=> (result == 32'd0)
    );

// When not in reset, result captures the previous cycle's a*b.
    check_result_captures_product: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (result == ($past(a) * $past(b)))
    );

// Zero on a forces zero on result on the next clock.
    check_zero_a_forces_zero_result: assert property (
        @(posedge clk) disable iff (reset)
        (a == 16'd0) |=> (result == 32'd0)
    );

// Zero on b forces zero on result on the next clock.
    check_zero_b_forces_zero_result: assert property (
        @(posedge clk) disable iff (reset)
        (b == 16'd0) |=> (result == 32'd0)
    );

// 1 on a passes b through to result on the next clock.
    check_one_a_passes_b: assert property (
        @(posedge clk) disable iff (reset)
        (a == 16'd1) |=> (result == $past(b))
    );

// 1 on b passes a through to result on the next clock.
    check_one_b_passes_a: assert property (
        @(posedge clk) disable iff (reset)
        (b == 16'd1) |=> (result == $past(a))
    );

endmodule
