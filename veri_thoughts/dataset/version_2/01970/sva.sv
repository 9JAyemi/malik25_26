module d_ff_asr_sva (
    input logic D,
    input logic S,
    input logic R,
    input logic CLK,
    input logic Q
);
    // Q at each cycle equals prior-cycle mux of S/R/D.
    check_state_equation: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |=> (Q == ($past(S) ? 1'b1 : ($past(R) ? 1'b0 : $past(D))))
    );

    // S high sets Q to 1 on the next cycle.
    check_set_forces_one: assert property (
        @(posedge CLK) disable iff (1'b0)
        S |=> (Q == 1'b1)
    );

    // R high with S low resets Q to 0 on the next cycle.
    check_reset_forces_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!S && R) |=> (Q == 1'b0)
    );

    // With S=0 and R=0, Q captures D on the next cycle.
    check_data_capture: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!S && !R) |=> (Q == $past(D))
    );

    // When S and R are both high, S has priority and Q becomes 1 next cycle.
    check_set_overrides_reset: assert property (
        @(posedge CLK) disable iff (1'b0)
        (S && R) |=> (Q == 1'b1)
    );

    // If idle last cycle (S=R=0) and D matched Q, Q must hold its value.
    check_no_spurious_change_when_idle: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |=> ((!$past(S) && !$past(R) && ($past(D) == $past(Q))) |-> (Q == $past(Q)))
    );
endmodule