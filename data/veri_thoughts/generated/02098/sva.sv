module DFFSR_sva (
    input logic Q,
    input logic C,
    input logic S,
    input logic R,
    input logic D
);
    // Clock: C (posedge). Reset: R is synchronous active-high driving Q to 0; S is synchronous active-high set to 1 (lower priority than R).
    // Logic: Sequential (edge-triggered DFF with synchronous set/reset).
    // Behavior: On posedge C: if R then Q<=0; else if S then Q<=1; else Q<=D.

    // R forces next Q to 0 on the following sample (synchronous reset).
    check_reset_forces_zero: assert property (
        @(posedge C) R |-> (Q == 1'b0)
    );

    // With R deasserted, S forces next Q to 1 (set).
    check_set_forces_one_no_reset: assert property (
        @(posedge C) disable iff (R) S |-> (Q == 1'b1)
    );

    // When both R and S are 1, next Q is 0 (reset has priority over set).
    check_reset_priority_over_set: assert property (
        @(posedge C) (R && S) |-> (Q == 1'b0)
    );

    // With both R and S deasserted, next Q equals D sampled at this clock.
    check_data_captured_when_no_set_reset: assert property (
        @(posedge C) (!R && !S) |-> (Q == $past(D))
    );

    // A 0->1 rise on Q must be caused by either S or by D=1 when no set/reset in the prior cycle.
    check_q_rise_cause: assert property (
        @(posedge C) $rose(Q) |-> (!$past(R) && ($past(S) || (!$past(S) && ($past(D) == 1'b1))))
    );

    // A 1->0 fall on Q must be caused by either R or by D=0 when no set in the prior cycle.
    check_q_fall_cause: assert property (
        @(posedge C) $fell(Q) |-> ($past(R) || (!$past(R) && !$past(S) && ($past(D) == 1'b0)))
    );

endmodule