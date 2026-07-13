module d_ff_reset_sva (
    input logic D,
    input logic RESET_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic CLK_N,
    input logic Q
);
    ///// Reset behavior /////
    // Active-low reset with valid power drives Q to 0 on the next clock.
    reset_low_forces_q0: assert property (
        @(posedge CLK_N) ((VPWR == 1'b1) && (VGND == 1'b0) && (!RESET_B)) |=> (Q == 1'b0)
    );

    // Reset low without valid power has no effect on Q (no assignment occurs).
    reset_low_without_power_no_effect: assert property (
        @(posedge CLK_N) ((!((VPWR == 1'b1) && (VGND == 1'b0))) && (!RESET_B)) |=> (Q == $past(Q))
    );

    ///// Data capture behavior /////
    // With valid power and reset deasserted, Q captures D on the next clock.
    capture_d_when_powered: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) ((VPWR == 1'b1) && (VGND == 1'b0) && (RESET_B == 1'b1)) |=> (Q == D)
    );

    // If D equals previous Q when capturing, Q remains unchanged.
    no_change_when_d_equals_prev_q: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) ((VPWR == 1'b1) && (VGND == 1'b0) && (RESET_B == 1'b1) && (D == $past(Q))) |=> (Q == $past(Q))
    );

    // If D differs from previous Q when capturing, Q must change.
    q_changes_when_d_differs_from_prev_q: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) ((VPWR == 1'b1) && (VGND == 1'b0) && (RESET_B == 1'b1) && (D != $past(Q))) |=> (Q != $past(Q))
    );

    ///// Hold behavior /////
    // With invalid power rails, Q holds its value across the clock.
    hold_when_power_invalid: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) (!((VPWR == 1'b1) && (VGND == 1'b0))) |=> (Q == $past(Q))
    );

    ///// Change qualification /////
    // Any change on Q must be preceded by valid power rails.
    q_change_requires_valid_power: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) $changed(Q) |-> $past((VPWR == 1'b1) && (VGND == 1'b0))
    );
endmodule