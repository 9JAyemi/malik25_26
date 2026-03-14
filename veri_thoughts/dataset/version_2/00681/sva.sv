module sky130_fd_sc_ls__o311ai_sva (
    input logic CLK,   // sampling clock for assertions
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // Analysis: No clock/reset in RTL; purely combinational. Function: Y = ~(C1 & B1 & (A1|A2|A3)).

    // Y equals NAND of {C1, B1, OR(A1,A2,A3)}.
    check_func_equivalence: assert property (
        @(posedge CLK) Y == ~(C1 & B1 & (A1 | A2 | A3))
    );

    // Y must be 1 whenever C1 is 0.
    check_y_high_when_c1_low: assert property (
        @(posedge CLK) (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Y must be 1 whenever B1 is 0.
    check_y_high_when_b1_low: assert property (
        @(posedge CLK) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // Y must be 1 when all A inputs are 0.
    check_y_high_when_all_a_low: assert property (
        @(posedge CLK) (!A1 && !A2 && !A3) |-> (Y == 1'b1)
    );

    // Y must be 0 when C1=1, B1=1, and any A input is 1.
    check_y_low_when_all_terms_high: assert property (
        @(posedge CLK) (C1 && B1 && (A1 | A2 | A3)) |-> (Y == 1'b0)
    );

    // If Y is 0, then C1=1, B1=1, and at least one A input is 1.
    check_y_zero_implies_all_terms_high: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (C1 && B1 && (A1 | A2 | A3))
    );

    // If any term is 0 (C1=0 or B1=0 or all A's 0), Y must be 1.
    check_y_one_when_any_term_low: assert property (
        @(posedge CLK) ((C1 == 1'b0) || (B1 == 1'b0) || (!A1 && !A2 && !A3)) |-> (Y == 1'b1)
    );

    // A falling edge of Y can occur only when all terms are 1 now.
    check_y_fall_requires_all_terms_high: assert property (
        @(posedge CLK) $fell(Y) |-> (C1 && B1 && (A1 | A2 | A3))
    );

    // A rising edge of Y can occur only when some term is 0 now.
    check_y_rise_requires_any_term_low: assert property (
        @(posedge CLK) $rose(Y) |-> ((C1 == 1'b0) || (B1 == 1'b0) || (!A1 && !A2 && !A3))
    );

    // With C1=B1=1, Y is the inversion of (A1|A2|A3).
    check_y_under_c1_b1_high: assert property (
        @(posedge CLK) (C1 && B1) |-> (Y == ~(A1 | A2 | A3))
    );
endmodule