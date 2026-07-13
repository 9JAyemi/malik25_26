module my_module_sva (
    input logic VPWR,
    input logic VGND,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    // Expected combinational function of X
    logic expected_X;
    assign expected_X = (A1 ^ A2) & ~(B1 & C1);

    // X matches its Boolean implementation.
    check_x_function: assert property (
        @(posedge A1) X == expected_X
    );

    // When B1 and C1 are both HIGH, X must be LOW.
    check_x_zero_when_B1C1_high: assert property (
        @(posedge B1) (B1 && C1) |-> (X == 1'b0)
    );

    // When A1 equals A2, X must be LOW.
    check_x_zero_when_A_equal: assert property (
        @(posedge A1) (A1 == A2) |-> (X == 1'b0)
    );

    // When (A1^A2) and not (B1 & C1), X must be HIGH.
    check_x_one_when_cond: assert property (
        @(posedge A1) ((A1 ^ A2) && !(B1 && C1)) |-> (X == 1'b1)
    );

    // If X is HIGH then A1^A2 must be HIGH.
    check_x_implies_xor: assert property (
        @(posedge A1) X |-> (A1 ^ A2)
    );

    // If X is HIGH then not(B1 & C1) must hold.
    check_x_implies_not_B1C1: assert property (
        @(posedge B1) X |-> !(B1 && C1)
    );

    // If B1 is LOW then X equals A1^A2.
    check_B1_zero_pass_through: assert property (
        @(posedge B1) (B1 == 1'b0) |-> (X == (A1 ^ A2))
    );

    // If C1 is LOW then X equals A1^A2.
    check_C1_zero_pass_through: assert property (
        @(posedge C1) (C1 == 1'b0) |-> (X == (A1 ^ A2))
    );

    // If B1 is HIGH and X is HIGH, then C1 must be LOW.
    check_x_and_B1_implies_not_C1: assert property (
        @(posedge B1) (X && (B1 == 1'b1)) |-> (C1 == 1'b0)
    );

    // If C1 is HIGH and X is HIGH, then B1 must be LOW.
    check_x_and_C1_implies_not_B1: assert property (
        @(posedge C1) (X && (C1 == 1'b1)) |-> (B1 == 1'b0)
    );

    // D1 does not affect X when A1,A2,B1,C1 are stable.
    check_D1_independence: assert property (
        @(posedge D1) $stable({A1,A2,B1,C1}) |-> $stable(X)
    );

    // VPWR does not affect X when A1,A2,B1,C1 are stable.
    check_VPWR_independence: assert property (
        @(posedge VPWR) $stable({A1,A2,B1,C1}) |-> $stable(X)
    );

    // VGND does not affect X when A1,A2,B1,C1 are stable.
    check_VGND_independence: assert property (
        @(posedge VGND) $stable({A1,A2,B1,C1}) |-> $stable(X)
    );
endmodule