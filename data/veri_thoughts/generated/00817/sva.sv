module sky130_fd_sc_ls__a221o_sva (
    input  logic clk,
    input  logic X,
    input  logic A1,
    input  logic A2,
    input  logic B1,
    input  logic B2,
    input  logic C1
);
    ///// Functional correctness /////
    // X must equal (A1 & A2 & C1) | (B1 & B2 & C1).
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((A1 && A2 && C1) || (B1 && B2 && C1))
    );

    // When C1 is LOW, X must be LOW.
    check_c1_low_forces_x0: assert property (
        @(posedge clk) (C1 == 1'b0) |-> (X == 1'b0)
    );

    // A-path alone (A1&A2 with C1) is sufficient to drive X HIGH.
    check_a_path_sufficient: assert property (
        @(posedge clk) (A1 && A2 && C1) |-> (X == 1'b1)
    );

    // B-path alone (B1&B2 with C1) is sufficient to drive X HIGH.
    check_b_path_sufficient: assert property (
        @(posedge clk) (B1 && B2 && C1) |-> (X == 1'b1)
    );

    // If X is HIGH, C1 must be HIGH.
    check_x_high_requires_c1: assert property (
        @(posedge clk) (X == 1'b1) |-> (C1 == 1'b1)
    );

    // If X is HIGH, at least one of (A1&A2) or (B1&B2) must be HIGH.
    check_x_high_requires_some_pair: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A1 && A2) || (B1 && B2))
    );

    // If C1 is HIGH and neither pair is HIGH, then X must be LOW.
    check_x_low_when_c1_high_and_no_pairs: assert property (
        @(posedge clk) (C1 && !(A1 && A2) && !(B1 && B2)) |-> (X == 1'b0)
    );

    // If both pairs and C1 are HIGH, X must be HIGH.
    check_both_pairs_and_c1_high: assert property (
        @(posedge clk) (C1 && (A1 && A2) && (B1 && B2)) |-> (X == 1'b1)
    );
endmodule