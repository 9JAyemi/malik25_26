module d_ff_reset_sva (
    input logic D,
    input logic CLK,
    input logic RESET_B,
    input logic Q
);
    // Analysis:
    // - Clock: CLK (posedge)
    // - Reset: RESET_B active-low, asynchronous; forces Q=0
    // - Logic: Sequential D flip-flop with async reset; Q captures D on CLK rising edge when RESET_B==1

    ///// Reset behavior /////
    // Reset low forces Q=0 at every clock edge.
    check_reset_low_forces_q0: assert property (
        @(posedge CLK) (!RESET_B) |-> (Q == 1'b0)
    );

    // Falling edge of RESET_B implies Q=0 at this clock.
    check_reset_fall_forces_q0: assert property (
        @(posedge CLK) $fell(RESET_B) |-> (Q == 1'b0)
    );

    // Rising edge of RESET_B keeps Q=0 in this cycle (assignment to D occurs after this edge).
    check_reset_rise_keeps_q0: assert property (
        @(posedge CLK) $rose(RESET_B) |-> (Q == 1'b0)
    );

    // While held in reset across cycles, Q stays stable.
    check_q_stable_while_in_reset: assert property (
        @(posedge CLK) ($past(RESET_B) == 1'b0 && RESET_B == 1'b0) |-> $stable(Q)
    );

    // While held in reset across cycles, Q remains 0.
    check_q_zero_while_in_reset: assert property (
        @(posedge CLK) ($past(RESET_B) == 1'b0 && RESET_B == 1'b0) |-> (Q == 1'b0)
    );

    ///// Non-reset invariants /////
    // Q=1 implies reset is deasserted.
    check_q1_implies_reset_high: assert property (
        @(posedge CLK) disable iff (!RESET_B) (Q == 1'b1) |-> (RESET_B == 1'b1)
    );

    // No rising edge on Q in the first cycle after reset is deasserted.
    check_no_q_rise_just_after_reset: assert property (
        @(posedge CLK) disable iff (!RESET_B) ($past(RESET_B) == 1'b0) |-> (!$rose(Q))
    );

    // No change on Q between cycles when reset stays asserted.
    check_no_q_change_across_held_reset: assert property (
        @(posedge CLK) ($past(RESET_B) == 1'b0 && RESET_B == 1'b0) |-> (Q == $past(Q))
    );

endmodule