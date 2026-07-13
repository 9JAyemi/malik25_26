module d_latch_sva (
    input logic CLK,
    input logic GATE,
    input logic D,
    input logic Q
);
    // Next-cycle state equation: if GATE is low at next edge, Q= D; else Q holds previous value.
    check_next_state_equation: assert property (
        @(posedge CLK) 1'b1 |=> (Q == ((!GATE) ? D : $past(Q)))
    );

    // When GATE is high, Q holds its previous sampled value into the next cycle.
    check_hold_when_gate_high: assert property (
        @(posedge CLK) GATE |=> (Q == $past(Q))
    );

    // Any observed change in Q between consecutive samples must be due to GATE being low in the previous cycle.
    check_q_change_requires_prev_gate_low: assert property (
        @(posedge CLK) $changed(Q) |-> $past(!GATE)
    );

    // If GATE is high and D toggles, Q still holds its previous value into the next cycle.
    check_hold_when_gate_high_even_if_d_toggles: assert property (
        @(posedge CLK) (GATE && (D != $past(D))) |=> (Q == $past(Q))
    );

    // On a rising transition of GATE (low->high), Q equals the D value captured in the prior cycle.
    check_q_matches_d_on_gate_rise: assert property (
        @(posedge CLK) $rose(GATE) |-> (Q == $past(D))
    );
endmodule