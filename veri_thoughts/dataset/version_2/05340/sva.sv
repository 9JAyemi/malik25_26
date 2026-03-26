module sky130_fd_sc_lp__xnor3_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X matches the 3-input XNOR of A, B, and C.
    check_xnor3_function: assert property (
        @(posedge clk) X === ~(A ^ B ^ C)
    );

    // With C low, X reduces to the XNOR of A and B.
    check_c_low_reduces_to_ab_xnor: assert property (
        @(posedge clk) (C == 1'b0) |-> (X === ~(A ^ B))
    );

    // With C high, X reduces to the XOR of A and B.
    check_c_high_reduces_to_ab_xor: assert property (
        @(posedge clk) (C == 1'b1) |-> (X === (A ^ B))
    );

    // When A and B are equal, X is the inversion of C.
    check_ab_equal_inverts_c: assert property (
        @(posedge clk) (A == B) |-> (X === ~C)
    );

    // When A and B differ, X follows C.
    check_ab_different_follows_c: assert property (
        @(posedge clk) (A != B) |-> (X === C)
    );

    // When B and C are equal, X is the inversion of A.
    check_bc_equal_inverts_a: assert property (
        @(posedge clk) (B == C) |-> (X === ~A)
    );

    // When B and C differ, X follows A.
    check_bc_different_follows_a: assert property (
        @(posedge clk) (B != C) |-> (X === A)
    );

    // When A and C are equal, X is the inversion of B.
    check_ac_equal_inverts_b: assert property (
        @(posedge clk) (A == C) |-> (X === ~B)
    );

    // When A and C differ, X follows B.
    check_ac_different_follows_b: assert property (
        @(posedge clk) (A != C) |-> (X === B)
    );

    // All-zero inputs must produce a high output.
    check_all_zero_case: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0 && C == 1'b0) |-> (X === 1'b1)
    );

    // All-one inputs must produce a low output.
    check_all_one_case: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1 && C == 1'b1) |-> (X === 1'b0)
    );

endmodule