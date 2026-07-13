module adder_sva (
    input logic clk,
    input logic signed [31:0] a,
    input logic signed [31:0] b,
    input logic signed [31:0] sum
);
    // Clock: clk. No reset in RTL. Sequential saturating signed adder.

    // Helper: 32-bit signed saturating add of x+y per RTL
    let sat_add(x, y) = (((x[31] == y[31]) && (((x + y)[31]) != x[31])) ? (x[31] ? 32'sh8000_0000 : 32'sh7fff_ffff) : (x + y));

    ///// Saturation behavior /////
    // Next-cycle sum equals saturating add of current a and b.
    check_saturating_sum: assert property (
        @(posedge clk) 1 |=> (sum == sat_add($past(a), $past(b)))
    );

    ///// No-overflow cases /////
    // If signs differ, next-cycle sum equals raw a+b (no overflow possible).
    check_no_overflow_opposite_signs: assert property (
        @(posedge clk) ($past(a)[31] != $past(b)[31]) |=> (sum == ($past(a) + $past(b)))
    );

    // If signs same and raw sum sign matches input sign, next-cycle sum equals raw a+b.
    check_no_overflow_same_sign_no_wrap: assert property (
        @(posedge clk) (($past(a)[31] == $past(b)[31]) && ((($past(a) + $past(b))[31]) == $past(a)[31])) |=> (sum == ($past(a) + $past(b)))
    );

    ///// Overflow saturation /////
    // Positive overflow (two positives producing negative) saturates to +MAX.
    check_positive_overflow_saturates_max: assert property (
        @(posedge clk) (($past(a)[31] == 1'b0) && ($past(b)[31] == 1'b0) && ((($past(a) + $past(b))[31]) == 1'b1)) |=> (sum == 32'sh7fff_ffff)
    );

    // Negative overflow (two negatives producing positive) saturates to -MIN.
    check_negative_overflow_saturates_min: assert property (
        @(posedge clk) (($past(a)[31] == 1'b1) && ($past(b)[31] == 1'b1) && ((($past(a) + $past(b))[31]) == 1'b0)) |=> (sum == 32'sh8000_0000)
    );

    ///// Basic arithmetic identities honored /////
    // 0 + 0 yields 0 on next cycle.
    check_zero_plus_zero: assert property (
        @(posedge clk) (($past(a) == 32'sd0) && ($past(b) == 32'sd0)) |=> (sum == 32'sd0)
    );

    // Adding zero on b passes a through on next cycle.
    check_add_zero_b_transparent: assert property (
        @(posedge clk) ($past(b) == 32'sd0) |=> (sum == $past(a))
    );

    // Adding zero on a passes b through on next cycle.
    check_add_zero_a_transparent: assert property (
        @(posedge clk) ($past(a) == 32'sd0) |=> (sum == $past(b))
    );

    // When no overflow, next-cycle sum sign matches raw sum sign.
    check_sign_matches_when_no_overflow: assert property (
        @(posedge clk)
            !((($past(a)[31] == $past(b)[31]) && ((($past(a) + $past(b))[31]) != $past(a)[31])))
            |=> (sum[31] == ($past(a) + $past(b))[31])
    );

endmodule