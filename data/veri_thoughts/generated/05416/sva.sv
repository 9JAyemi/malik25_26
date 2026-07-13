module absolute_value_calculator_sva #(
    parameter n = 8
) (
    input  logic                 clk,
    input  logic signed [n-1:0]  num,
    input  logic        [n-1:0]  abs_num
);

    // abs_num must match the RTL conditional expression.
    check_abs_matches_rtl: assert property (
        @(posedge clk)
        abs_num == ((num[n-1] == 1'b1) ? (~num + 1'b1) : num)
    );

    // Negative inputs must produce the two's-complement magnitude.
    check_negative_input_twos_complement: assert property (
        @(posedge clk)
        num[n-1] |-> (abs_num == (~num + 1'b1))
    );

    // Non-negative inputs must pass through unchanged.
    check_nonnegative_input_passthrough: assert property (
        @(posedge clk)
        !num[n-1] |-> (abs_num == num)
    );

    // Zero must map to zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk)
        (num == '0) |-> (abs_num == '0)
    );

    // The most-negative value wraps to itself in fixed width.
    check_min_negative_maps_to_self: assert property (
        @(posedge clk)
        (num == {1'b1, {(n-1){1'b0}}}) |-> (abs_num == {1'b1, {(n-1){1'b0}}})
    );

    // Any other negative input must yield a non-negative result.
    check_non_min_negative_result_sign_clear: assert property (
        @(posedge clk)
        (num[n-1] && (num != {1'b1, {(n-1){1'b0}}})) |-> (abs_num[n-1] == 1'b0)
    );

endmodule