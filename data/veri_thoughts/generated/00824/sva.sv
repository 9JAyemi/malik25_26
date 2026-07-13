module my_or3b_4_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C_N,
    input logic X
);
    // X equals the structural expression implemented in RTL.
    check_structural_equivalence: assert property (
        @(posedge CLK) X == ((A | B | C_N) & (A | C_N) & (B | C_N))
    );

    // X equals the simplified boolean form C_N | (A & B).
    check_simplified_equivalence: assert property (
        @(posedge CLK) X == (C_N | (A & B))
    );

    // When C_N is 1, X must be 1.
    check_cn_dominates: assert property (
        @(posedge CLK) C_N |-> (X == 1'b1)
    );

    // When C_N is 0, X must equal A & B.
    check_cn0_means_and: assert property (
        @(posedge CLK) (!C_N) |-> (X == (A & B))
    );

    // When C_N is 0 and A is 0, X must be 0.
    check_cn0_a0_forces_x0: assert property (
        @(posedge CLK) (!C_N && !A) |-> (X == 1'b0)
    );

    // When C_N is 0 and B is 0, X must be 0.
    check_cn0_b0_forces_x0: assert property (
        @(posedge CLK) (!C_N && !B) |-> (X == 1'b0)
    );

    // When both A and B are 1, X must be 1.
    check_ab_high_implies_x1: assert property (
        @(posedge CLK) (A && B) |-> (X == 1'b1)
    );

    // If X is 1, then at least one of A, B, or C_N is 1.
    check_x_implies_any_input_or_cn: assert property (
        @(posedge CLK) X |-> (A | B | C_N)
    );

    // If X is 1, then A or C_N must be 1.
    check_x_implies_a_or_cn: assert property (
        @(posedge CLK) X |-> (A | C_N)
    );

    // If X is 1, then B or C_N must be 1.
    check_x_implies_b_or_cn: assert property (
        @(posedge CLK) X |-> (B | C_N)
    );
endmodule