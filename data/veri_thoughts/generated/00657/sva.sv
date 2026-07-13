module four_input_and_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic not_A,
    input logic not_B,
    input logic not_C,
    input logic not_D,
    input logic nor_AB,
    input logic nor_CD,
    input logic nor_ABCD
);

    ///// Gate-level correctness /////
    // not_A is the inversion of A.
    check_not_A: assert property (
        @(posedge $global_clock) (not_A === ~A)
    );

    // not_B is the inversion of B.
    check_not_B: assert property (
        @(posedge $global_clock) (not_B === ~B)
    );

    // not_C is the inversion of C.
    check_not_C: assert property (
        @(posedge $global_clock) (not_C === ~C)
    );

    // not_D is the inversion of D.
    check_not_D: assert property (
        @(posedge $global_clock) (not_D === ~D)
    );

    // nor_AB is NOR of not_A and not_B.
    check_nor_AB: assert property (
        @(posedge $global_clock) (nor_AB === ~(not_A | not_B))
    );

    // nor_CD is NOR of not_C and not_D.
    check_nor_CD: assert property (
        @(posedge $global_clock) (nor_CD === ~(not_C | not_D))
    );

    // nor_ABCD is NOR of nor_AB and nor_CD.
    check_nor_ABCD: assert property (
        @(posedge $global_clock) (nor_ABCD === ~(nor_AB | nor_CD))
    );

    // X is inversion of nor_ABCD.
    check_X_from_nor_ABCD: assert property (
        @(posedge $global_clock) (X === ~nor_ABCD)
    );

    ///// Functional equivalence /////
    // X equals the 4-input AND of A, B, C, and D.
    check_functional_and: assert property (
        @(posedge $global_clock) (X === (A & B & C & D))
    );

endmodule