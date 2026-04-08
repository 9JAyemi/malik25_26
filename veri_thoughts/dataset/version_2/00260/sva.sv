module system_auto_cc_0_wr_status_flags_as_16_sva (
    input logic ram_full_fb_i_reg_0,
    input logic [0:0] E,
    input logic s_axi_wready,
    input logic gic0_gc0_count_d1_reg_3,
    input logic s_aclk,
    input logic out,
    input logic s_axi_wvalid,
    input logic [0:0] Q,
    input logic [0:0] gnxpm_cdc_rd_pntr_bin_reg_3
);

    // s_axi_wready is hardwired high.
    check_wready_constant_high: assert property (
        @(posedge s_aclk) s_axi_wready == 1'b1
    );

    // E can only assert when s_axi_wvalid is high.
    check_e_requires_wvalid: assert property (
        @(posedge s_aclk) E[0] |-> s_axi_wvalid
    );

    // Without s_axi_wvalid, both observable outputs driven by the full flag stay low.
    check_no_wvalid_forces_outputs_low: assert property (
        @(posedge s_aclk) !s_axi_wvalid |-> (!E[0] && !ram_full_fb_i_reg_0)
    );

    // The feedback output is E gated by Q and the read pointer bit.
    check_feedback_output_equation: assert property (
        @(posedge s_aclk) ram_full_fb_i_reg_0 == (E[0] & Q[0] & gnxpm_cdc_rd_pntr_bin_reg_3[0])
    );

    // The feedback output can only assert when E is asserted.
    check_feedback_requires_e: assert property (
        @(posedge s_aclk) ram_full_fb_i_reg_0 |-> E[0]
    );

    // Loading a 1 into the internal flag makes E track s_axi_wvalid on the next cycle.
    check_load_one_makes_e_track_wvalid: assert property (
        @(posedge s_aclk)
        (out || (!out && gic0_gc0_count_d1_reg_3)) |=> (E[0] == s_axi_wvalid)
    );

    // Loading a 1 into the internal flag makes the feedback output track its gates next cycle.
    check_load_one_makes_feedback_track_gates: assert property (
        @(posedge s_aclk)
        (out || (!out && gic0_gc0_count_d1_reg_3)) |=> (ram_full_fb_i_reg_0 == (s_axi_wvalid & Q[0] & gnxpm_cdc_rd_pntr_bin_reg_3[0]))
    );

    // Loading a 0 into the internal flag clears both observable outputs on the next cycle.
    check_load_zero_clears_outputs: assert property (
        @(posedge s_aclk)
        (!out && !gic0_gc0_count_d1_reg_3) |=> (!E[0] && !ram_full_fb_i_reg_0)
    );

endmodule