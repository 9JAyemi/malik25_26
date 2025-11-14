
module system_auto_cc_0_wr_status_flags_as_16 (
  output ram_full_fb_i_reg_0,
  output [0:0] E,
  output s_axi_wready,
  input gic0_gc0_count_d1_reg_3,
  input s_aclk,
  input out,
  input s_axi_wvalid,
  input [0:0] Q,
  input [0:0] gnxpm_cdc_rd_pntr_bin_reg_3
);

  wire [0:0] E;
  wire [0:0] Q;
  wire gic0_gc0_count_d1_reg_3;
  wire [0:0] gnxpm_cdc_rd_pntr_bin_reg_3;
  wire out;
  wire ram_full_fb_i;
  reg ram_full_fb_i_reg = 0;
  wire ram_full_fb_i_reg_1;
  wire ram_full_i = 0;
  wire s_aclk;
  wire s_axi_wready;
  wire s_axi_wvalid;

  // LUT2 module instantiation
  assign E = s_axi_wvalid & ram_full_fb_i_reg;

  // FDPE module instantiation for ram_full_fb_i_reg
  always @(posedge s_aclk)
    if (out)
      ram_full_fb_i_reg <= 1'b1;
    else
      ram_full_fb_i_reg <= gic0_gc0_count_d1_reg_3;

  // LUT4 module instantiation
  assign ram_full_fb_i_reg_1 = ram_full_fb_i_reg & s_axi_wvalid & Q & gnxpm_cdc_rd_pntr_bin_reg_3;

  // LUT1 module instantiation
  assign s_axi_wready = !ram_full_i;
  assign ram_full_fb_i_reg_0 = ram_full_fb_i_reg_1;

endmodule