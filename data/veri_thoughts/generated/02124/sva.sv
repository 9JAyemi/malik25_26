module nand4_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Analysis: no clock/reset; pure combinational; Y = (A & B) | (C & D); power pins unused by logic.

    // Y equals (A & B) | (C & D).
    check_function_posA: assert property (
        @(posedge A) Y === ((A & B) | (C & D))
    );

    // Y must be 1 when A and B are both 1.
    check_y_high_when_ab11: assert property (
        @(posedge B) (A==1'b1 && B==1'b1) |-> (Y==1'b1)
    );

    // Y must be 1 when C and D are both 1.
    check_y_high_when_cd11: assert property (
        @(posedge D) (C==1'b1 && D==1'b1) |-> (Y==1'b1)
    );

    // Y must be 0 when B=0 and D=0.
    check_y_zero_when_b0_d0: assert property (
        @(posedge B) (B==1'b0 && D==1'b0) |-> (Y==1'b0)
    );

    // When B=1 and C=0 and D=0, Y equals A.
    check_y_equals_a_when_b1_cd00: assert property (
        @(posedge A) (B==1'b1 && C==1'b0 && D==1'b0) |-> (Y===A)
    );

    // When D=1 and A=0 and B=0, Y equals C.
    check_y_equals_c_when_d1_ab00: assert property (
        @(posedge C) (D==1'b1 && A==1'b0 && B==1'b0) |-> (Y===C)
    );

    // Y must be 0 when all inputs are 0.
    check_y_zero_all_zero: assert property (
        @(posedge A) (A==1'b0 && B==1'b0 && C==1'b0 && D==1'b0) |-> (Y==1'b0)
    );

    // Y must be 1 when all inputs are 1.
    check_y_one_all_one: assert property (
        @(posedge A) (A==1'b1 && B==1'b1 && C==1'b1 && D==1'b1) |-> (Y==1'b1)
    );

    // If A=0 and B=0, Y reduces to C & D.
    check_y_depends_on_cd_when_ab00: assert property (
        @(posedge A) (A==1'b0 && B==1'b0) |-> (Y === (C & D))
    );

    // If C=0 and D=0, Y reduces to A & B.
    check_y_depends_on_ab_when_cd00: assert property (
        @(posedge C) (C==1'b0 && D==1'b0) |-> (Y === (A & B))
    );
endmodule