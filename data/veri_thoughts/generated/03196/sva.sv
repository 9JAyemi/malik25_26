module adder_sva (
    input logic signed [7:0] input_a,
    input logic signed [7:0] input_b,
    input logic reset,
    input logic signed [8:0] sum
);

    // No explicit RTL clock; use $global_clock for formal sampling.
    // reset is active-high and the DUT is combinational.

    // reset forces the output to zero.
    check_reset_forces_zero: assert property (
        @($global_clock) reset |-> (sum == 9'sd0)
    );

    // when reset is low, sum matches the RTL addition expression.
    check_sum_matches_rtl_expression: assert property (
        @($global_clock) disable iff (reset)
        (sum == (input_a + input_b))
    );

    // when reset is low, the 9-bit output is sign-extended from the 8-bit result.
    check_sum_is_sign_extended: assert property (
        @($global_clock) disable iff (reset)
        (sum[8] == sum[7])
    );

endmodule