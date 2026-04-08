module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] s,
    input logic overflow,
    input logic overflow_detected
);

    // Sum output must match the 8-bit addition of a and b.
    check_sum_matches_adder: assert property (
        @(posedge clk) disable iff (reset) s == (a + b)
    );

    // Overflow must match the implemented signed overflow expression.
    check_overflow_matches_expression: assert property (
        @(posedge clk) disable iff (reset) overflow == ((a[7] == b[7]) && (a[7] != s[7]))
    );

    // Overflow indicator must be a direct copy of overflow.
    check_indicator_matches_overflow: assert property (
        @(posedge clk) disable iff (reset) overflow_detected == overflow
    );

    // Opposite-sign inputs cannot produce signed overflow.
    check_no_overflow_with_opposite_sign_inputs: assert property (
        @(posedge clk) disable iff (reset) (a[7] != b[7]) |-> !overflow
    );

    // Any reported overflow requires both inputs to have the same sign.
    check_overflow_requires_same_input_signs: assert property (
        @(posedge clk) disable iff (reset) overflow |-> (a[7] == b[7])
    );

    // Any reported overflow requires the sum sign to differ from the input sign.
    check_overflow_requires_result_sign_change: assert property (
        @(posedge clk) disable iff (reset) overflow |-> (s[7] != a[7])
    );

    // Positive plus positive yielding negative must assert overflow.
    check_positive_overflow_case: assert property (
        @(posedge clk) disable iff (reset) ((a[7] == 1'b0) && (b[7] == 1'b0) && (s[7] == 1'b1)) |-> overflow
    );

    // Negative plus negative yielding positive must assert overflow.
    check_negative_overflow_case: assert property (
        @(posedge clk) disable iff (reset) ((a[7] == 1'b1) && (b[7] == 1'b1) && (s[7] == 1'b0)) |-> overflow
    );

endmodule