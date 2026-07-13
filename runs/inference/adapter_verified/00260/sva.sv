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

// E must equal s_axi_wvalid AND ram_full_fb_i_reg.
    check_e_definition: assert property (
        @(posedge s_aclk) E == (s_axi_wvalid & ram_full_fb_i_reg)
    );

// s_axi_wready must be the inverse of ram_full_i (always 0 in RTL).
    check_wready_inverse: assert property (
        @(posedge s_aclk) s_axi_wready == !ram_full_i
    );

// ram_full_fb_i_reg_0 must equal E.
    check_ram_full_fb_i_reg_0_definition: assert property (
        @(posedge s_aclk) ram_full_fb_i_reg_0 == E
    );

// When out is high, ram_full_fb_i_reg must be set on the next cycle.
    check_ram_full_fb_i_reg_set_on_out_high: assert property (
        @(posedge s_aclk) out |=> ram_full_fb_i_reg
    );

// When out is low, ram_full_fb_i_reg must follow gic0_gc0_count_d1_reg_3 on the next cycle.
    check_ram_full_fb_i_reg_capture_on_out_low: assert property (
        @(posedge s_aclk) !out |=> (ram_full_fb_i_reg == gic0_gc0_count_d1_reg_3)
    );

// E can only be high when ram_full_fb_i_reg is high.
    check_e_implies_ram_full_fb_i_reg: assert property (
        @(posedge s_aclk) E |-> ram_full_fb_i_reg
    );

// E can only be high when s_axi_wvalid is high.
    check_e_implies_wvalid: assert property (
        @(posedge s_aclk) E |-> s_axi_wvalid
    );

// A high E must drive ram_full_fb_i_reg_0 high on the next cycle.
    check_ram_full_fb_i_reg_0_on_e: assert property (
        @(posedge s_aclk) E |=> ram_full_fb_i_reg_0
    );

// A low E must drive ram_full_fb_i_reg_0 low on the next cycle.
    check_ram_full_fb_i_reg_0_off_e: assert property (
        @(posedge s_aclk) !E |=> !ram_full_fb_i_reg_0
    );

endmodule
