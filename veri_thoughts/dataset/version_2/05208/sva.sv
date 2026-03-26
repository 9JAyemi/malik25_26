module sky130_fd_sc_lp__sdfrtp_4_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic RESET_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Active-low reset forces Q low.
    check_reset_forces_q_low: assert property (
        @(posedge CLK)
        !RESET_B |-> (Q == 1'b0)
    );

    // Q is still low on the first sampled cycle after reset was active.
    check_post_reset_q_low: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!$initstate && ($past(RESET_B) == 1'b0)) |-> (Q == 1'b0)
    );

    // SCD low clears Q on the next sampled clock.
    check_scd_low_clears_q: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (SCD == 1'b0) |=> (Q == 1'b0)
    );

    // With SCD high and SCE high, Q captures D.
    check_enabled_capture_updates_q: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        ((SCD == 1'b1) && (SCE == 1'b1)) |=> (Q == $past(D))
    );

    // With SCD high and SCE low, Q holds its previous value.
    check_hold_when_capture_disabled: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        ((SCD == 1'b1) && (SCE == 1'b0)) |=> (Q == $past(Q))
    );

    // A rising Q must come from an enabled capture of 1.
    check_q_rise_requires_capture_one: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!$initstate && $rose(Q)) |-> (($past(RESET_B) == 1'b1) &&
                                       ($past(SCD) == 1'b1) &&
                                       ($past(SCE) == 1'b1) &&
                                       ($past(D) == 1'b1))
    );

    // A falling Q must come from reset, clear, or an enabled capture of 0.
    check_q_fall_requires_zero_update: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (!$initstate && $fell(Q)) |-> (($past(RESET_B) == 1'b0) ||
                                       ($past(SCD) == 1'b0) ||
                                       (($past(SCD) == 1'b1) &&
                                        ($past(SCE) == 1'b1) &&
                                        ($past(D) == 1'b0)))
    );

endmodule