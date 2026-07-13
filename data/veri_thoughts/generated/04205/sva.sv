module top_module_assertions (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] s,
    input logic overflow,
    input logic [7:0] out
);

    // Sum output is the 8-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @(posedge clk) s == (a + b)
    );

    // Overflow follows the signed addition overflow rule.
    check_overflow_matches_sign_rule: assert property (
        @(posedge clk) overflow == ((a[7] == b[7]) && (a[7] != s[7]))
    );

    // XOR stage applies the fixed 8'hAA mask to the sum.
    check_xor_output_matches_sum: assert property (
        @(posedge clk) out == (s ^ 8'hAA)
    );

    // Top output matches add-then-xor behavior from the inputs.
    check_out_matches_add_then_xor: assert property (
        @(posedge clk) out == ((a + b) ^ 8'hAA)
    );

    // Mixed-sign additions do not assert overflow.
    check_no_overflow_for_mixed_sign_inputs: assert property (
        @(posedge clk) (a[7] != b[7]) |-> !overflow
    );

    // Two positive inputs producing a negative sum must assert overflow.
    check_positive_overflow_case: assert property (
        @(posedge clk) ((a[7] == 1'b0) && (b[7] == 1'b0) && (s[7] == 1'b1)) |-> overflow
    );

    // Two negative inputs producing a positive sum must assert overflow.
    check_negative_overflow_case: assert property (
        @(posedge clk) ((a[7] == 1'b1) && (b[7] == 1'b1) && (s[7] == 1'b0)) |-> overflow
    );

endmodule