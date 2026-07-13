module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out_final
);

    // out_final must equal the AND of the two XOR terms.
    check_out_final_function: assert property (
        @(posedge clk) out_final == ((a ^ b) & (c ^ d))
    );

    // If both XOR terms are high, out_final must be high.
    check_out_final_high_when_both_terms_high: assert property (
        @(posedge clk) ((a ^ b) & (c ^ d)) |-> out_final
    );

    // If either XOR term is low, out_final must be low.
    check_out_final_low_when_any_term_low: assert property (
        @(posedge clk) (!((a ^ b) & (c ^ d))) |-> !out_final
    );

    // A high out_final requires both XOR terms to be high.
    check_out_final_high_requires_both_terms_high: assert property (
        @(posedge clk) out_final |-> ((a ^ b) & (c ^ d))
    );

    // A low out_final requires at least one XOR term to be low.
    check_out_final_low_requires_any_term_low: assert property (
        @(posedge clk) !out_final |-> (!((a ^ b) & (c ^ d)))
    );

endmodule