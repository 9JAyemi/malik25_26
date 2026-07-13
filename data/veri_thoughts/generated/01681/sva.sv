module dff_sva (
    input logic D,
    input logic C,
    input logic S,
    input logic R,
    input logic Q
);
    // Clock: C posedge. S: sync set (active-high). R: sync reset (active-high). Sequential flop.

    // S asserted at clock edge forces Q=1 on next clock.
    check_set_forces_one: assert property (
        @(posedge C) S |=> (Q == 1'b1)
    );

    // R asserted without S forces Q=0 on next clock.
    check_reset_forces_zero_when_not_set: assert property (
        @(posedge C) (!S && R) |=> (Q == 1'b0)
    );

    // When both S and R asserted, S has priority and Q=1 next clock.
    check_set_has_priority_over_reset: assert property (
        @(posedge C) (S && R) |=> (Q == 1'b1)
    );

    // With neither S nor R, Q_next equals prior D.
    check_follows_d_when_no_sr: assert property (
        @(posedge C) disable iff (R) (!S && !R) |=> (Q == $past(D))
    );

    // With neither S nor R and D==Q, Q holds its value.
    check_hold_when_no_sr_and_d_eq_q: assert property (
        @(posedge C) disable iff (R) (!S && !R && (D == Q)) |=> $stable(Q)
    );

    // With neither S nor R and D!=Q, Q toggles to prior D.
    check_toggle_when_no_sr_and_d_neq_q: assert property (
        @(posedge C) disable iff (R) (!S && !R && (D != Q)) |=> (Q != $past(Q) && Q == $past(D))
    );

    // Next-state equation: Q_next = (S ? 1 : (R ? 0 : D)).
    check_next_state_equation: assert property (
        @(posedge C) 1'b1 |=> (Q == ($past(S) ? 1'b1 : ($past(R) ? 1'b0 : $past(D))))
    );

endmodule