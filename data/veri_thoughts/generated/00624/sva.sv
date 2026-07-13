module Problem4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic X
);
    // Combinational DUT with no clock/reset; sample assertions on posedge A.

    // X equals the RTL sum-of-products function.
    check_function_equivalence: assert property (
        @(posedge A)
        X == ((~A & ~B & ~C & D & ~E) |
              (~A & ~B & ~C & D & E) |
              (~A & ~B & C & ~D & E) |
              (~A & ~B & C & D & E) |
              (~A & B & ~C & ~D & E) |
              (~A & B & ~C & D & E) |
              (~A & B & C & ~D & E) |
              (A & ~B & ~C & ~D & E) |
              (A & ~B & ~C & D & E) |
              (A & ~B & C & D & E) |
              (A & B & C & ~D & E) |
              (A & B & C & D & E))
    );

    // When E=0, X equals (~A & ~B & ~C & D).
    check_E0_equivalence: assert property (
        @(posedge A) (E == 1'b0) |-> (X == (~A & ~B & ~C & D))
    );

    // With E=1 and A=0,B=0,C=1, X is 1 regardless of D.
    check_E1_A0B0C1_true: assert property (
        @(posedge A) (E && ~A && ~B && C) |-> (X == 1'b1)
    );

    // With E=1 and A=0,B=1,C=0, X is 1 regardless of D.
    check_E1_A0B1C0_true: assert property (
        @(posedge A) (E && ~A && B && ~C) |-> (X == 1'b1)
    );

    // With E=1 and A=1,B=0,C=0, X is 1 regardless of D.
    check_E1_A1B0C0_true: assert property (
        @(posedge A) (E && A && ~B && ~C) |-> (X == 1'b1)
    );

    // With E=1 and A=1,B=1,C=1, X is 1 regardless of D.
    check_E1_A1B1C1_true: assert property (
        @(posedge A) (E && A && B && C) |-> (X == 1'b1)
    );

    // With E=1 and A=1,B=1,C=0, X is always 0.
    check_E1_A1B1C0_false: assert property (
        @(posedge A) (E && A && B && ~C) |-> (X == 1'b0)
    );

    // With E=1 and A=1,B=0,C=1,D=1, X must be 1.
    check_E1_A1B0C1_D1_true: assert property (
        @(posedge A) (E && A && ~B && C && D) |-> (X == 1'b1)
    );

    // With E=1 and A=1,B=0,C=1,D=0, X must be 0.
    check_E1_A1B0C1_D0_false: assert property (
        @(posedge A) (E && A && ~B && C && ~D) |-> (X == 1'b0)
    );

    // With E=1 and A=0,B=0,C=0,D=1, X must be 1.
    check_E1_A0B0C0_D1_true: assert property (
        @(posedge A) (E && ~A && ~B && ~C && D) |-> (X == 1'b1)
    );

    // With E=1 and A=0,B=0,C=0,D=0, X must be 0.
    check_E1_A0B0C0_D0_false: assert property (
        @(posedge A) (E && ~A && ~B && ~C && ~D) |-> (X == 1'b0)
    );
endmodule