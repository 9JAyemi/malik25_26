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

    // E is the AND of the write valid and the registered full flag.
    check_e_matches_valid_and_full: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E == {1'b0} || (E == {1'b1} && s_axi_wvalid && ram_full_fb_i_reg)
    );

    // s_axi_wready is tied low by the RTL.
    check_wready_tied_low: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        s_axi_wready == 1'b0
    );

    // ram_full_fb_i_reg_0 is the registered full flag gated by E.
    check_ram_full_fb_i_reg_0_matches_e: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg_0 == (E && ram_full_fb_i_reg)
    );

    // A high E requires the write valid signal to be high.
    check_e_requires_valid: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E[0] |-> s_axi_wvalid
    );

    // A high E requires the registered full flag to be high.
    check_e_requires_full: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        E[0] |-> ram_full_fb_i_reg
    );

    // A high registered full flag requires E to be high.
    check_full_requires_e: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg |-> E[0]
    );

    // A high registered full flag requires the write valid signal to be high.
    check_full_requires_valid: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg |-> s_axi_wvalid
    );

    // A high registered full flag requires the E gated full output to be high.
    check_full_requires_ram_full_fb_i_reg_0: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        ram_full_fb_i_reg |-> ram_full_fb_i_reg_0
    );

    // A low E forces the registered full flag low.
    check_e_low_clears_full: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        !E[0] |-> !ram_full_fb_i_reg
    );

    // A low E forces the gated full output low.
    check_e_low_clears_ram_full_fb_i_reg_0: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        !E[0] |-> !ram_full_fb_i_reg_0
    );

    // A high write valid with a low registered full flag forces E low.
    check_valid_without_full_sets_e_low: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        (s_axi_wvalid && !ram_full_fb_i_reg) |-> !E[0]
    );

    // A high write valid with a low gated full output forces E low.
    check_valid_without_ram_full_fb_i_reg_0_sets_e_low: assert property (
        @(posedge s_aclk) disable iff (1'b0)
        (s_axi_wvalid && !ram_full_fb_i_reg_0) |-> !E[0]
    );

endmodule