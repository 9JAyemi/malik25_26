module sky130_fd_sc_ls__a222o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);
    // Combinational cell with no clock/reset; sample on any port edge.

    // X equals (A1&A2) | (B1&B2) | (C1&C2).
    check_functional_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or posedge C2 or negedge C2 or
          posedge X  or negedge X)
        X == ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

    // If only A-pair is high, X must be high.
    check_A_pair_dominates: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or posedge C2 or negedge C2 or
          posedge X  or negedge X)
        (!((A1 & A2) & ~(B1 & B2) & ~(C1 & C2)) || (X == 1'b1))
    );

    // If only B-pair is high, X must be high.
    check_B_pair_dominates: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or posedge C2 or negedge C2 or
          posedge X  or negedge X)
        (!((B1 & B2) & ~(A1 & A2) & ~(C1 & C2)) || (X == 1'b1))
    );

    // If only C-pair is high, X must be high.
    check_C_pair_dominates: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or posedge C2 or negedge C2 or
          posedge X  or negedge X)
        (!((C1 & C2) & ~(A1 & A2) & ~(B1 & B2)) || (X == 1'b1))
    );

    // If no pair is high, X must be low.
    check_no_pair_implies_X_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or posedge C2 or negedge C2 or
          posedge X  or negedge X)
        (((A1 & A2) | (B1 & B2) | (C1 & C2)) || (X == 1'b0))
    );

    // If X is high, at least one pair must be high.
    check_X_high_implies_some_pair: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or posedge C2 or negedge C2 or
          posedge X  or negedge X)
        (!(X == 1'b1) || ((A1 & A2) | (B1 & B2) | (C1 & C2)))
    );

    // If X is low, no pair can be high.
    check_X_low_implies_no_pair: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1 or posedge C2 or negedge C2 or
          posedge X  or negedge X)
        (!(X == 1'b0) || (~(A1 & A2) & ~(B1 & B2) & ~(C1 & C2)))
    );
endmodule