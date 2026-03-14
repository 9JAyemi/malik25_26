module top_module_sva (
    input logic CLK,
    input logic D,
    input logic SET,
    input logic CLR,
    input logic Q,
    input logic Q_N
);
    // Clock: CLK (posedge). No reset signal present.
    // Sequential logic: posedge-triggered DFF with synchronous SET (priority) and CLR.
    // Behavior: If SET=1 -> Q=1; else if CLR=1 -> Q=0; else Q<=D. Q_N is always ~Q.

    ///// Output relationship /////
    // Q_N is always the inversion of Q.
    check_qn_is_inversion_of_q: assert property (
        @(posedge CLK) (Q_N == ~Q)
    );

    ///// Priority rules /////
    // When both SET and CLR are 1, SET dominates and Q goes HIGH next cycle.
    check_set_dominates_clr: assert property (
        @(posedge CLK) (SET && CLR) |=> (Q == 1'b1) && (Q_N == 1'b0)
    );

    ///// Set/Clear effects /////
    // SET drives Q HIGH on the next clock, regardless of D.
    check_set_forces_q_high: assert property (
        @(posedge CLK) SET |=> (Q == 1'b1)
    );

    // With CLR asserted and SET deasserted, Q goes LOW on the next clock.
    check_clr_forces_q_low_when_no_set: assert property (
        @(posedge CLK) (CLR && !SET) |=> (Q == 1'b0)
    );

    // With CLR asserted and SET deasserted, Q_N goes HIGH on the next clock.
    check_clr_sets_qn_high_when_no_set: assert property (
        @(posedge CLK) (CLR && !SET) |=> (Q_N == 1'b1)
    );

    ///// Data capture /////
    // When neither SET nor CLR, Q captures D on the next clock.
    check_d_captured_into_q_on_next_clk: assert property (
        @(posedge CLK) (!SET && !CLR) |=> (Q == $past(D))
    );

    // When neither SET nor CLR, Q_N captures inverted D on the next clock.
    check_d_captured_into_qn_on_next_clk: assert property (
        @(posedge CLK) (!SET && !CLR) |=> (Q_N == ~$past(D))
    );

    ///// Functional equivalence /////
    // Full next-state function for Q: priority SET over CLR over D.
    check_full_next_state_q: assert property (
        @(posedge CLK) 1'b1 |=> (Q == $past(SET ? 1'b1 : (CLR ? 1'b0 : D)))
    );

    ///// Hold behavior (derived from data capture) /////
    // If neither SET nor CLR and D equals current Q, Q holds its value next cycle.
    check_hold_when_d_equals_q: assert property (
        @(posedge CLK) (!SET && !CLR && (D == Q)) |=> (Q == $past(Q))
    );

endmodule