module sky130_fd_sc_ms__maj3_sva (
    // DUT ports
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    // Internal nets from RTL (for structural checks)
    input logic or0_out,
    input logic and0_out,
    input logic and1_out,
    input logic or1_out_X
);
    // Analysis: no clock/reset in RTL; purely combinational majority-of-3 (X = AB + AC + BC). Using $global_clock for SVA sampling.

    ///// Structural wiring checks /////
    // X must equal the buffered or1_out_X.
    check_buf_connects_output: assert property (
        @(posedge $global_clock) (X == or1_out_X)
    );

    // or1_out_X must be the OR of and1_out and and0_out.
    check_or1_combines_and0_and1: assert property (
        @(posedge $global_clock) (or1_out_X == (and1_out | and0_out))
    );

    // and1_out must be A & B.
    check_and1_is_A_and_B: assert property (
        @(posedge $global_clock) (and1_out == (A & B))
    );

    // or0_out must be A | B.
    check_or0_is_A_or_B: assert property (
        @(posedge $global_clock) (or0_out == (A | B))
    );

    // and0_out must be or0_out & C.
    check_and0_is_or0_and_C: assert property (
        @(posedge $global_clock) (and0_out == (or0_out & C))
    );

    ///// Functional majority behavior /////
    // X must equal the 2-of-3 majority of A,B,C.
    check_majority_equation: assert property (
        @(posedge $global_clock) (X == ((A & B) | (A & C) | (B & C)))
    );

    // If A and B are 1, X must be 1 (independent of C).
    check_two_high_AB_sets_X: assert property (
        @(posedge $global_clock) ((A & B) |-> X)
    );

    // If A and C are 1, X must be 1 (independent of B).
    check_two_high_AC_sets_X: assert property (
        @(posedge $global_clock) ((A & C) |-> X)
    );

    // If B and C are 1, X must be 1 (independent of A).
    check_two_high_BC_sets_X: assert property (
        @(posedge $global_clock) ((B & C) |-> X)
    );

    // If exactly one high (A only), X must be 0.
    check_exactly_one_A_sets_X0: assert property (
        @(posedge $global_clock) (( A & !B & !C) |-> (X == 1'b0))
    );

    // If exactly one high (B only), X must be 0.
    check_exactly_one_B_sets_X0: assert property (
        @(posedge $global_clock) ((!A &  B & !C) |-> (X == 1'b0))
    );

    // If exactly one high (C only), X must be 0.
    check_exactly_one_C_sets_X0: assert property (
        @(posedge $global_clock) ((!A & !B &  C) |-> (X == 1'b0))
    );

    // If all three are 0, X must be 0.
    check_all_zero_sets_X0: assert property (
        @(posedge $global_clock) ((!A & !B & !C) |-> (X == 1'b0))
    );

    // If all three are 1, X must be 1.
    check_all_one_sets_X1: assert property (
        @(posedge $global_clock) ((A & B & C) |-> (X == 1'b1))
    );

endmodule