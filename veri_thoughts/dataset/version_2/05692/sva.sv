module top_module_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] s,
    input logic overflow,
    input logic result
);

    // Sum output matches the 8-bit addition of the inputs.
    check_sum_matches_addition: assert property (
        @(posedge clk) s == (a + b)
    );

    // Overflow follows the RTL signed overflow equation.
    check_overflow_matches_rtl_formula: assert property (
        @(posedge clk) overflow == ((a[7] == b[7]) && (a[7] != s[7]))
    );

    // Mixed-sign operands cannot produce signed overflow.
    check_no_overflow_on_mixed_signs: assert property (
        @(posedge clk) (a[7] != b[7]) |-> (overflow == 1'b0)
    );

    // Two positive operands producing a negative sum must assert overflow.
    check_positive_overflow_case: assert property (
        @(posedge clk) ((a[7] == 1'b0) && (b[7] == 1'b0) && (s[7] == 1'b1)) |-> (overflow == 1'b1)
    );

    // Two negative operands producing a positive sum must assert overflow.
    check_negative_overflow_case: assert property (
        @(posedge clk) ((a[7] == 1'b1) && (b[7] == 1'b1) && (s[7] == 1'b0)) |-> (overflow == 1'b1)
    );

    // Result matches the RTL XNOR-style sign/overflow relation.
    check_result_matches_formula: assert property (
        @(posedge clk) result == ~(s[7] ^ overflow)
    );

    // Result is low when the sum sign and overflow differ.
    check_result_low_on_sign_overflow_mismatch: assert property (
        @(posedge clk) (s[7] != overflow) |-> (result == 1'b0)
    );

    // Result is high when the sum sign and overflow match.
    check_result_high_on_sign_overflow_match: assert property (
        @(posedge clk) (s[7] == overflow) |-> (result == 1'b1)
    );

endmodule