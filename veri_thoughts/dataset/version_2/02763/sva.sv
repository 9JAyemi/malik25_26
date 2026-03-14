module and4b_sva (
    input logic CLK,   // external checker clock; DUT has no clock/reset
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // X equals NAND of A_N, B, C, D.
    check_function_nand_equivalence: assert property (
        @(posedge CLK) X == ~(A_N & B & C & D)
    );

    // When all inputs are HIGH, X must be LOW.
    check_all_high_implies_X_low: assert property (
        @(posedge CLK) (A_N && B && C && D) |-> (X == 1'b0)
    );

    // When any input is LOW, X must be HIGH.
    check_any_low_implies_X_high: assert property (
        @(posedge CLK) ((!A_N) || (!B) || (!C) || (!D)) |-> (X == 1'b1)
    );

    // If X is LOW, then all inputs must be HIGH.
    check_X_low_implies_all_high: assert property (
        @(posedge CLK) (X == 1'b0) |-> (A_N && B && C && D)
    );

    // If X is HIGH, then at least one input is LOW.
    check_X_high_implies_any_low: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((!A_N) || (!B) || (!C) || (!D))
    );

    // With B,C,D HIGH, X equals NOT A_N.
    check_dep_A: assert property (
        @(posedge CLK) (B && C && D) |-> (X == ~A_N)
    );

    // With A_N,C,D HIGH, X equals NOT B.
    check_dep_B: assert property (
        @(posedge CLK) (A_N && C && D) |-> (X == ~B)
    );

    // With A_N,B,D HIGH, X equals NOT C.
    check_dep_C: assert property (
        @(posedge CLK) (A_N && B && D) |-> (X == ~C)
    );

    // With A_N,B,C HIGH, X equals NOT D.
    check_dep_D: assert property (
        @(posedge CLK) (A_N && B && C) |-> (X == ~D)
    );

endmodule