module flip_flop_sva (
    input  logic D,
    input  logic SCD,
    input  logic SCE,
    input  logic RESET_B,  // Active-low async reset
    input  logic VPWR,
    input  logic VGND,
    input  logic VPB,
    input  logic VNB,
    input  logic Q,
    input  logic CLK
);
    // Reset low forces Q to 0 at every clock.
    reset_low_forces_zero: assert property (
        @(posedge CLK) (!RESET_B) |-> (Q == 1'b0)
    );

    // A falling edge on RESET_B clears Q to 0 by the next clock sample.
    reset_fall_clears_Q: assert property (
        @(posedge CLK) $fell(RESET_B) |-> (Q == 1'b0)
    );

    // With SCE HIGH, Q captures D on the next clock.
    capture_on_sce_high: assert property (
        @(posedge CLK) disable iff (!RESET_B) SCE |=> (Q == $past(D))
    );

    // With SCE LOW, Q holds its previous value.
    hold_on_sce_low: assert property (
        @(posedge CLK) disable iff (!RESET_B) !SCE |=> (Q == $past(Q))
    );

    // If SCE HIGH and D equals previous Q, Q does not change next cycle.
    sce_high_same_data_no_change: assert property (
        @(posedge CLK) disable iff (!RESET_B) (SCE && (D == $past(Q))) |=> (Q == $past(Q))
    );

    // If SCE HIGH and D differs from previous Q, Q must change next cycle.
    sce_high_diff_data_changes_q: assert property (
        @(posedge CLK) disable iff (!RESET_B) (SCE && (D != $past(Q))) |=> $changed(Q)
    );

    // Any Q change without a RESET_B fall implies prior SCE was HIGH.
    q_change_requires_sce_no_reset_edge: assert property (
        @(posedge CLK) disable iff (!RESET_B) ($changed(Q) && !$fell(RESET_B)) |-> $past(SCE)
    );

    // When SCE is LOW, SCD activity does not affect Q on the next clock.
    scd_change_no_effect_when_sce_low: assert property (
        @(posedge CLK) disable iff (!RESET_B) (!SCE && $changed(SCD)) |=> (Q == $past(Q))
    );

    // Next-state equation when no reset fall occurred in the interval.
    next_state_equation_without_reset_edge: assert property (
        @(posedge CLK) disable iff (!RESET_B) (!$fell(RESET_B)) |-> (Q == ($past(SCE) ? $past(D) : $past(Q)))
    );

    // After reset deasserts and with SCE LOW, Q remains 0 on the next clock.
    post_reset_release_no_load_holds_zero: assert property (
        @(posedge CLK) ($rose(RESET_B) && !SCE) |=> (Q == 1'b0)
    );
endmodule