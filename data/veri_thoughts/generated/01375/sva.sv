module system_auto_cc_0_wr_status_flags_as_82_sva (
    input logic ram_full_fb_i_reg_0,
    input logic [0:0] E,
    input logic s_axi_arready,
    input logic [3:0] gic0_gc0_count_d1_reg_3,
    input logic s_aclk,
    input logic out,
    input logic s_axi_arvalid,
    input logic [0:0] Q,
    input logic [3:0] gnxpm_cdc_rd_pntr_bin_reg_3
);
    // s_axi_arready equals the LSB of gic0_gc0_count_d1_reg_3.
    check_arready_lsb_map: assert property (
        @(posedge s_aclk) s_axi_arready == gic0_gc0_count_d1_reg_3[0]
    );

    // ram_full_fb_i_reg_0 is s_axi_arvalid & Q[0] & gnxpm_cdc_rd_pntr_bin_reg_3[0].
    check_ram_full_fb_and_gating: assert property (
        @(posedge s_aclk) ram_full_fb_i_reg_0 == (s_axi_arvalid & Q[0] & gnxpm_cdc_rd_pntr_bin_reg_3[0])
    );

    // E equals s_axi_arvalid & ram_full_fb_i_reg_0.
    check_E_equals_arvalid_and_ramfull: assert property (
        @(posedge s_aclk) E[0] == (s_axi_arvalid & ram_full_fb_i_reg_0)
    );

    // E equals s_axi_arvalid & Q[0] & gnxpm_cdc_rd_pntr_bin_reg_3[0].
    check_E_equals_flat_and: assert property (
        @(posedge s_aclk) E[0] == (s_axi_arvalid & Q[0] & gnxpm_cdc_rd_pntr_bin_reg_3[0])
    );

    // When s_axi_arvalid is 0, ram_full_fb_i_reg_0 and E are 0 in the same cycle.
    check_arvalid_low_clears_outputs: assert property (
        @(posedge s_aclk) !s_axi_arvalid |-> (ram_full_fb_i_reg_0 == 1'b0 && E[0] == 1'b0)
    );

    // When Q[0] is 0, ram_full_fb_i_reg_0 and E are 0 in the same cycle.
    check_Q_low_clears_outputs: assert property (
        @(posedge s_aclk) !Q[0] |-> (ram_full_fb_i_reg_0 == 1'b0 && E[0] == 1'b0)
    );

    // When gnxpm_cdc_rd_pntr_bin_reg_3[0] is 0, ram_full_fb_i_reg_0 and E are 0 in the same cycle.
    check_ptr_lsb_low_clears_outputs: assert property (
        @(posedge s_aclk) (gnxpm_cdc_rd_pntr_bin_reg_3[0] == 1'b0) |-> (ram_full_fb_i_reg_0 == 1'b0 && E[0] == 1'b0)
    );

    // If E is 1, then s_axi_arvalid, Q[0], and gnxpm_cdc_rd_pntr_bin_reg_3[0] are 1 in the same cycle.
    check_E_high_implies_inputs_high: assert property (
        @(posedge s_aclk) E[0] |-> (s_axi_arvalid && Q[0] && gnxpm_cdc_rd_pntr_bin_reg_3[0])
    );

    // If ram_full_fb_i_reg_0 is 1, then s_axi_arvalid, Q[0], and gnxpm_cdc_rd_pntr_bin_reg_3[0] are 1 in the same cycle.
    check_ramfull_high_implies_inputs_high: assert property (
        @(posedge s_aclk) ram_full_fb_i_reg_0 |-> (s_axi_arvalid && Q[0] && gnxpm_cdc_rd_pntr_bin_reg_3[0])
    );
endmodule