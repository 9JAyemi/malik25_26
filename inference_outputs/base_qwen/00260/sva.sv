module system_auto_cc_0_wr_status_flags_as_16_sva (
    input logic s_aclk,
    input logic out,
    input logic s_axi_wvalid,
    input logic Q,
    input logic gnxpm_cdc_rd_pntr_bin_reg_3,
    output logic ram_full_fb_i_reg_0
);
    // Sequential logic for ram_full_fb_i_reg
    sequential_logic_1: assert property (
        @(posedge s_aclk) disable iff (!out) ram_full_fb_i_reg |-> ram_full_fb_i_reg_1
    );

    // Combinational logic for E
    combinational_logic_1: assert property (
        @(posedge s_aclk) disable iff (!out) E |-> s_axi_wvalid & ram_full_fb_i_reg
    );

    // Combinational logic for s_axi_wready
    combinational_logic_2: assert property (
        @(posedge s_aclk) disable iff (!out) s_axi_wready |-> !ram_full_i
    );

    // Combinational logic for ram_full_fb_i_reg_0
    combinational_logic_3: assert property (
        @(posedge s_aclk) disable iff (!out) ram_full_fb_i_reg_0 |-> ram_full_fb_i_reg_1
    );
endmodule