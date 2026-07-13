module sky130_fd_sc_lp__nand4_sva (
    input logic CLK,   // Sampling clock (DUT has no clock/reset; purely combinational)
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    ///// Functional equivalence /////
    // Y equals the 4-input NAND of A,B,C,D.
    check_y_is_nand4: assert property (
        @(posedge CLK) Y == ~(A & B & C & D)
    );

    ///// Truth table implications /////
    // If all inputs are 1, Y must be 0.
    check_all_ones_implies_y0: assert property (
        @(posedge CLK) (A && B && C && D) |-> (Y == 1'b0)
    );
    // If A is 0, Y must be 1.
    check_a0_implies_y1: assert property (
        @(posedge CLK) (A == 1'b0) |-> (Y == 1'b1)
    );
    // If B is 0, Y must be 1.
    check_b0_implies_y1: assert property (
        @(posedge CLK) (B == 1'b0) |-> (Y == 1'b1)
    );
    // If C is 0, Y must be 1.
    check_c0_implies_y1: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Y == 1'b1)
    );
    // If D is 0, Y must be 1.
    check_d0_implies_y1: assert property (
        @(posedge CLK) (D == 1'b0) |-> (Y == 1'b1)
    );
    // Y can be 0 only when all inputs are 1.
    check_y0_implies_all_ones: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (A && B && C && D)
    );

    ///// Edge-driven behavior when last input goes HIGH /////
    // When A rises and B,C,D are stably 1, Y must be 0.
    check_y_fall_when_A_rises_last: assert property (
        @(posedge CLK) $rose(A) && B && C && D && $past(B) && $past(C) && $past(D) |-> (Y == 1'b0)
    );
    // When B rises and A,C,D are stably 1, Y must be 0.
    check_y_fall_when_B_rises_last: assert property (
        @(posedge CLK) $rose(B) && A && C && D && $past(A) && $past(C) && $past(D) |-> (Y == 1'b0)
    );
    // When C rises and A,B,D are stably 1, Y must be 0.
    check_y_fall_when_C_rises_last: assert property (
        @(posedge CLK) $rose(C) && A && B && D && $past(A) && $past(B) && $past(D) |-> (Y == 1'b0)
    );
    // When D rises and A,B,C are stably 1, Y must be 0.
    check_y_fall_when_D_rises_last: assert property (
        @(posedge CLK) $rose(D) && A && B && C && $past(A) && $past(B) && $past(C) |-> (Y == 1'b0)
    );
endmodule