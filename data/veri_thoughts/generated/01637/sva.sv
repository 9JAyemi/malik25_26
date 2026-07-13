module combinational_logic_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic Y
);
    // X equals A || B || (C && !D)
    check_X_function: assert property (
        @(posedge CLK) disable iff (1'b0) X == (A || B || (C && !D))
    );

    // Y equals !A && (!B || (C && D))
    check_Y_function: assert property (
        @(posedge CLK) disable iff (1'b0) Y == ((!A) && ((!B) || (C && D)))
    );

    // When A is 1, X=1 and Y=0
    check_A_forces_outputs: assert property (
        @(posedge CLK) disable iff (1'b0) A |-> (X == 1'b1) && (Y == 1'b0)
    );

    // When A is 0, X equals B || (C && !D)
    check_notA_X_definition: assert property (
        @(posedge CLK) disable iff (1'b0) (!A) |-> (X == (B || (C && !D)))
    );

    // When A is 0, Y equals !B || (C && D)
    check_notA_Y_definition: assert property (
        @(posedge CLK) disable iff (1'b0) (!A) |-> (Y == ((!B) || (C && D)))
    );

    // When A=0 and B=1, X=1 and Y=(C && D)
    check_notA_B1: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && B) |-> (X == 1'b1) && (Y == (C && D))
    );

    // When A=0 and B=0, X=(C && !D) and Y=1
    check_notA_B0: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && !B) |-> (X == (C && !D)) && (Y == 1'b1)
    );

    // When A=0 and C=0, X=B and Y=!B
    check_notA_C0: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && !C) |-> (X == B) && (Y == !B)
    );

    // When A=0, C=1, D=0, X=1 and Y=!B
    check_notA_C1_D0: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && C && !D) |-> (X == 1'b1) && (Y == !B)
    );

    // When A=0, C=1, D=1, X=B and Y=1
    check_notA_C1_D1: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && C && D) |-> (X == B) && (Y == 1'b1)
    );
endmodule