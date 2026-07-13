module sky130_fd_sc_hdll__sdfxtp_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // While VGND (active-low reset) is asserted, Q must be 0 on every clock.
    reset_level_holds_low: assert property (
        @(posedge CLK) (VGND == 1'b0) |-> (Q == 1'b0)
    );

    // On a clock when VGND is low, next-cycle Q remains 0 due to the reset branch.
    reset_sync_branch_clears: assert property (
        @(posedge CLK) (VGND == 1'b0) |=> (Q == 1'b0)
    );

    // Next-cycle Q equals: 1 if SCD=1, else 0 if SCE=1, else D (all sampled this cycle).
    q_next_follows_priority_mux: assert property (
        @(posedge CLK) disable iff (!VGND)
            1'b1 |=> ( $past(SCD) ? (Q == 1'b1) :
                       ($past(SCE) ? (Q == 1'b0) :
                                     (Q == $past(D))) )
    );

    // SCD=1 forces next-cycle Q=1 (highest priority).
    scd_forces_one: assert property (
        @(posedge CLK) disable iff (!VGND) SCD |=> (Q == 1'b1)
    );

    // With SCD=0, SCE=1 forces next-cycle Q=0.
    sce_forces_zero_when_no_scd: assert property (
        @(posedge CLK) disable iff (!VGND) (SCD == 1'b0 && SCE == 1'b1) |=> (Q == 1'b0)
    );

    // With SCD=0 and SCE=0, next-cycle Q captures D from this cycle.
    data_captured_when_ctrls_low: assert property (
        @(posedge CLK) disable iff (!VGND) (SCD == 1'b0 && SCE == 1'b0) |=> (Q == $past(D))
    );

    // When both SCD and SCE are 1, SCD has priority and next-cycle Q=1.
    priority_scd_over_sce: assert property (
        @(posedge CLK) disable iff (!VGND) (SCD == 1'b1 && SCE == 1'b1) |=> (Q == 1'b1)
    );

    // If controls are low and D equals previous Q, Q holds its value next cycle.
    hold_when_ctrls_low_and_d_eq_prev_q: assert property (
        @(posedge CLK) disable iff (!VGND) (SCD == 1'b0 && SCE == 1'b0 && D == $past(Q)) |=> (Q == $past(Q))
    );

endmodule