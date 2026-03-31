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

    // E must equal the AND of write valid, ram_full_fb_i_reg, Q, and the read pointer.
    check_e_matches_and: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E == (s_axi_wvalid & ram_full_fb_i_reg & Q & gnxpm_cdc_rd_pntr_bin_reg_3)
    );

    // s_axi_wready must always be high because ram_full_i is tied low.
    check_wready_always_high: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        s_axi_wready == 1'b1
    );

    // ram_full_fb_i_reg_0 must mirror the internal ram_full_fb_i_reg_1 value.
    check_reg0_matches_internal: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg_0 == (ram_full_fb_i_reg & s_axi_wvalid & Q & gnxpm_cdc_rd_pntr_bin_reg_3)
    );

    // A high E requires the write valid, ram_full_fb_i_reg, Q, and read pointer to be high.
    check_e_requires_all_inputs: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E == 1'b1 |-> (s_axi_wvalid && ram_full_fb_i_reg && Q && gnxpm_cdc_rd_pntr_bin_reg_3)
    );

    // All high inputs must drive E high.
    check_all_inputs_drive_e: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        (s_axi_wvalid && ram_full_fb_i_reg && Q && gnxpm_cdc_rd_pntr_bin_reg_3) |-> (E == 1'b1)
    );

    // A low E means at least one required input is low.
    check_e_low_requires_some_input_low: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E == 1'b0 |-> (!s_axi_wvalid || !ram_full_fb_i_reg || !Q || !gnxpm_cdc_rd_pntr_bin_reg_3)
    );

    // A high E requires ram_full_fb_i_reg to be high.
    check_e_requires_ram_full_reg: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E == 1'b1 |-> ram_full_fb_i_reg
    );

    // A high E requires write valid to be high.
    check_e_requires_write_valid: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E == 1'b1 |-> s_axi_wvalid
    );

    // A high E requires Q to be high.
    check_e_requires_q: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E == 1'b1 |-> Q
    );

    // A high E requires the read pointer to be high.
    check_e_requires_read_pointer: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E == 1'b1 |-> gnxpm_cdc_rd_pntr_bin_reg_3
    );

    // A high ram_full_fb_i_reg_0 requires ram_full_fb_i_reg to be high.
    check_reg0_requires_ram_full_reg: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg_0 |-> ram_full_fb_i_reg
    );

    // A high ram_full_fb_i_reg_0 requires write valid to be high.
    check_reg0_requires_write_valid: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg_0 |-> s_axi_wvalid
    );

    // A high ram_full_fb_i_reg_0 requires Q to be high.
    check_reg0_requires_q: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg_0 |-> Q
    );

    // A high ram_full_fb_i_reg_0 requires the read pointer to be high.
    check_reg0_requires_read_pointer: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg_0 |-> gnxpm_cdc_rd_pntr_bin_reg_3
    );

endmodule