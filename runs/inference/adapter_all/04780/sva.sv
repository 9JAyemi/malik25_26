module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out_final
);

    // out_final matches the XOR of a and b ANDed with the XOR of c and d.
    check_out_final_function: assert property (
        @(posedge clk) out_final == ((a ^ b) & (c ^ d))
    );

    // If a equals b, the first XOR term is zero and out_final must be zero.
    check_a_eq_b_forces_zero: assert property (
        @(posedge clk) (a == b) |-> (out_final == 1'b0)
    );

    // If c equals d, the second XOR term is zero and out_final must be zero.
    check_c_eq_d_forces_zero: assert property (
        @(posedge clk) (c == d) |-> (out_final == 1'b0)
    );

    // If both XOR terms are one, out_final must be one.
    check_both_xor_terms_one_sets_out: assert property (
        @(posedge clk) ((a ^ b) && (c ^ d)) |-> (out_final == 1'b1)
    );

    // If out_final is one, both XOR terms must be one.
    check_out_one_requires_both_xor_terms_one: assert property (
        @(posedge clk) out_final |-> ((a ^ b) && (c ^ d))
    );

    // If out_final is zero, at least one XOR term must be zero.
    check_out_zero_requires_some_xor_term_zero: assert property (
        @(posedge clk) !out_final |-> (!(a ^ b) || !(c ^ d))
    );

    // If a and c are equal, out_final reduces to b AND d.
    check_a_eq_c_reduces_to_b_and_d: assert property (
        @(posedge clk) (a == c) |-> (out_final == (b & d))
    );

    // If a and d are equal, out_final reduces to b AND c.
    check_a_eq_d_reduces_to_b_and_c: assert property (
        @(posedge clk) (a == d) |-> (out_final == (b & c))
    );

    // If b and c are equal, out_final reduces to a AND d.
    check_b_eq_c_reduces_to_a_and_d: assert property (
        @(posedge clk) (b == c) |-> (out_final == (a & d))
    );

    // If b and d are equal, out_final reduces to a AND c.
    check_b_eq_d_reduces_to_a_and_c: assert property (
        @(posedge clk) (b == d) |-> (out_final == (a & c))
    );

endmodule