module sky130_fd_sc_hd__lpflow_inputisolatch_sva (
    input logic D,
    input logic SLEEP_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Q,
    input logic Q_reg,
    input logic D_reg,
    input logic SLEEP_B_reg,
    input logic VPWR_reg,
    input logic VGND_reg,
    input logic VPB_reg,
    input logic VNB_reg
);

    // Q is always the continuous image of Q_reg.
    check_q_matches_q_reg: assert property (
        @(posedge VPWR or negedge VGND) Q == Q_reg
    );

    // Ground low holds Q and Q_reg low.
    check_q_low_when_vgnd_low: assert property (
        @(posedge VPWR) (VGND == 1'b0) |-> ((Q == 1'b0) && (Q_reg == 1'b0))
    );

    // Ground low clears all mirrored input registers.
    check_mirror_regs_low_when_vgnd_low: assert property (
        @(posedge VPWR) (VGND == 1'b0) |->
            ((D_reg == 1'b0) &&
             (SLEEP_B_reg == 1'b0) &&
             (VPWR_reg == 1'b0) &&
             (VGND_reg == 1'b0) &&
             (VPB_reg == 1'b0) &&
             (VNB_reg == 1'b0))
    );

    // With ground high, D_reg follows D.
    check_d_reg_follows_d: assert property (
        @(posedge VPWR) disable iff (VGND == 1'b0) (D_reg == D)
    );

    // With ground high, the other mirrored inputs follow their pins.
    check_side_regs_follow_inputs: assert property (
        @(posedge VPWR) disable iff (VGND == 1'b0)
            ((SLEEP_B_reg == SLEEP_B) &&
             (VGND_reg == VGND) &&
             (VPB_reg == VPB) &&
             (VNB_reg == VNB))
    );

    // Each enabled power edge loads the sampled D_reg value into Q.
    check_q_captures_d_reg_on_power_edge: assert property (
        @(posedge VPWR or negedge VGND) disable iff (VGND == 1'b0)
            1'b1 |=> (Q == $past(D_reg))
    );

    // Each enabled power edge loads the sampled D_reg value into Q_reg.
    check_qreg_captures_d_reg_on_power_edge: assert property (
        @(posedge VPWR or negedge VGND) disable iff (VGND == 1'b0)
            1'b1 |=> (Q_reg == $past(D_reg))
    );

    // A falling ground event leaves Q and Q_reg low by the next sample.
    check_vgnd_fall_clears_q: assert property (
        @(posedge VPWR or negedge VGND) $fell(VGND) |=> ((Q == 1'b0) && (Q_reg == 1'b0))
    );

endmodule