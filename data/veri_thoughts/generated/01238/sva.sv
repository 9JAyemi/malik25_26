module sky130_fd_sc_lp__a21bo_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);
    // Functional equivalence: X == (~B1_N) | (A1 & A2).
    check_functional_equivalence: assert property (
        @(posedge CLK) X == ((~B1_N) | (A1 & A2))
    );

    // B1_N low forces X high regardless of A1/A2.
    check_b1n_low_forces_x_high: assert property (
        @(posedge CLK) (B1_N == 1'b0) |-> (X == 1'b1)
    );

    // When B1_N is high, X equals A1 & A2.
    check_b1n_high_passes_and: assert property (
        @(posedge CLK) (B1_N == 1'b1) |-> (X == (A1 & A2))
    );

    // With B1_N high and A1 low, X must be low.
    check_a1_low_clears_x_when_b1n_high: assert property (
        @(posedge CLK) (B1_N && !A1) |-> (X == 1'b0)
    );

    // With B1_N high and A2 low, X must be low.
    check_a2_low_clears_x_when_b1n_high: assert property (
        @(posedge CLK) (B1_N && !A2) |-> (X == 1'b0)
    );

    // With B1_N high and both A1 and A2 high, X must be high.
    check_both_high_sets_x_when_b1n_high: assert property (
        @(posedge CLK) (B1_N && A1 && A2) |-> (X == 1'b1)
    );

    // If X is low then B1_N is high and not both A1 and A2 are high.
    check_x_low_implies_conditions: assert property (
        @(posedge CLK) (X == 1'b0) |-> (B1_N && !(A1 && A2))
    );

    // If X is high then either B1_N is low or both A1 and A2 are high.
    check_x_high_implies_conditions: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((!B1_N) || (A1 && A2))
    );
endmodule