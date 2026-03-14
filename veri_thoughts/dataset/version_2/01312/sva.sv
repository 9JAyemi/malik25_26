module my_logic_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // No clock/reset in RTL; pure combinational. Sample on posedge A1.
    // Functional relation: Y == ~(C1 & B1 & (A1 | A2 | A3)).

    // Y must equal NAND of C1, B1, and (A1|A2|A3).
    check_y_nand_equiv: assert property (
        @(posedge A1) Y == ~(C1 & B1 & (A1 | A2 | A3))
    );

    // When all NAND inputs are 1, Y must be 0.
    check_y_low_when_all_high: assert property (
        @(posedge A1) (C1 && B1 && (A1 || A2 || A3)) |-> (Y == 1'b0)
    );

    // If C1 is 0, Y must be 1 (NAND short-circuit).
    check_y_high_if_C1_low: assert property (
        @(posedge A1) (!C1) |-> (Y == 1'b1)
    );

    // If B1 is 0, Y must be 1 (NAND short-circuit).
    check_y_high_if_B1_low: assert property (
        @(posedge A1) (!B1) |-> (Y == 1'b1)
    );

    // If all A inputs are 0, Y must be 1.
    check_y_high_if_all_A_low: assert property (
        @(posedge A1) (!A1 && !A2 && !A3) |-> (Y == 1'b1)
    );

    // If A1=1 and C1=B1=1, Y must be 0.
    check_y_low_if_A1_high_and_enables: assert property (
        @(posedge A1) (A1 && C1 && B1) |-> (Y == 1'b0)
    );

    // If A2=1 and C1=B1=1, Y must be 0.
    check_y_low_if_A2_high_and_enables: assert property (
        @(posedge A1) (A2 && C1 && B1) |-> (Y == 1'b0)
    );

    // If A3=1 and C1=B1=1, Y must be 0.
    check_y_low_if_A3_high_and_enables: assert property (
        @(posedge A1) (A3 && C1 && B1) |-> (Y == 1'b0)
    );

    // With C1=B1=1, Y equals the inverse of (A1|A2|A3).
    check_y_complements_or_when_enables: assert property (
        @(posedge A1) (C1 && B1) |-> (Y == ~(A1 | A2 | A3))
    );

    // If Y is 0, then C1=1, B1=1, and at least one A is 1.
    check_y_low_implies_inputs_high: assert property (
        @(posedge A1) (Y == 1'b0) |-> (C1 && B1 && (A1 || A2 || A3))
    );

endmodule