module dff_ctrl_sva (
    input logic Q,
    input logic D,
    input logic CLK,
    input logic SET,
    input logic SLEEP_B,
    input logic NOTIFIER,
    input logic KAPWR,
    input logic VGND,
    input logic VPWR
);
    // Clock: CLK; Reset: SET active-low asynchronous.
    // Mixed logic: sequential DFF for Q; combinational Q_int unused externally.
    // Behavior: Q <= D on posedge CLK when SET=1; Q forced to 0 whenever SET=0.

    ///// Asynchronous reset behavior /////
    // While SET is low, Q must be 0 at each clock edge.
    async_reset_forces_q0_now: assert property (
        @(posedge CLK) (SET == 1'b0) |-> (Q == 1'b0)
    );

    // If SET was low at the previous clock, Q must be 0 now.
    prev_reset_low_implies_q0_now: assert property (
        @(posedge CLK) disable iff ($initstate)
            ($past(SET) == 1'b0) |-> (Q == 1'b0)
    );

    // If SET stayed low across consecutive clocks, Q stays 0.
    reset_held_two_cycles_keeps_q0: assert property (
        @(posedge CLK) disable iff ($initstate)
            (($past(SET) == 1'b0) && (SET == 1'b0)) |-> (Q == 1'b0)
    );

    ///// Functional update rules /////
    // When SET is high and D is 0 at a clock edge, Q must be 0 at the next clock.
    d0_when_set_high_drives_q0_next: assert property (
        @(posedge CLK) disable iff ($initstate || (SET == 1'b0))
            (SET && (D == 1'b0)) |-> ##1 (Q == 1'b0)
    );

    // If Q is 1 at a clock edge, the previous clock must have had SET=1 and D=1.
    q_high_requires_prev_set_and_d_high: assert property (
        @(posedge CLK) disable iff ($initstate || (SET == 1'b0))
            (Q == 1'b1) |-> ($past(SET) && $past(D))
    );

endmodule