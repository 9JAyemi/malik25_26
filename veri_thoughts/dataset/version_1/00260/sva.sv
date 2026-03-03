// SVA for system_auto_cc_0_wr_status_flags_as_16
// Focused, concise checks and coverage

module system_auto_cc_0_wr_status_flags_as_16_sva (
  input logic                     s_aclk,
  input logic                     out,
  input logic                     gic0_gc0_count_d1_reg_3,
  input logic                     s_axi_wvalid,
  input logic       [0:0]         Q,
  input logic       [0:0]         gnxpm_cdc_rd_pntr_bin_reg_3,
  input logic       [0:0]         E,
  input logic                     s_axi_wready,
  input logic                     ram_full_fb_i_reg_0,
  input logic                     ram_full_fb_i_reg,
  input logic                     ram_full_fb_i_reg_1
);

  // establish a safe start after first clock
  bit got_clk;
  always @(posedge s_aclk) got_clk <= 1'b1;

  default clocking cb @(posedge s_aclk); endclocking

  // X/Z free on key outputs and state
  assert property (cb !$isunknown({E, s_axi_wready, ram_full_fb_i_reg_0, ram_full_fb_i_reg}));

  // Combinational equivalences (sampled on clock)
  assert property (cb E == (s_axi_wvalid & ram_full_fb_i_reg));
  assert property (cb ram_full_fb_i_reg_1 == (ram_full_fb_i_reg & s_axi_wvalid & Q & gnxpm_cdc_rd_pntr_bin_reg_3));
  assert property (cb ram_full_fb_i_reg_0 == ram_full_fb_i_reg_1);

  // s_axi_wready must always be 1 (ram_full_i is hard 0)
  assert property (cb s_axi_wready == 1'b1);

  // Sequential behavior of ram_full_fb_i_reg
  // out=1 synchronously sets the flop to 1 on next cycle
  assert property (disable iff (!got_clk) cb out |=> ram_full_fb_i_reg == 1'b1);

  // out=0 makes the flop follow gic0_gc0_count_d1_reg_3 on next cycle
  assert property (disable iff (!got_clk) cb !out |=> ram_full_fb_i_reg == $past(gic0_gc0_count_d1_reg_3));

  // Functional coverage
  cover property (disable iff (!got_clk) cb out ##1 ram_full_fb_i_reg);
  cover property (disable iff (!got_clk) cb !out ##1 (ram_full_fb_i_reg == $past(gic0_gc0_count_d1_reg_3)));
  cover property (cb E);
  cover property (cb ram_full_fb_i_reg_0);
  cover property (cb $rose(ram_full_fb_i_reg));
  cover property (cb $fell(ram_full_fb_i_reg));

endmodule

bind system_auto_cc_0_wr_status_flags_as_16
  system_auto_cc_0_wr_status_flags_as_16_sva sva_i (
    .s_aclk(s_aclk),
    .out(out),
    .gic0_gc0_count_d1_reg_3(gic0_gc0_count_d1_reg_3),
    .s_axi_wvalid(s_axi_wvalid),
    .Q(Q),
    .gnxpm_cdc_rd_pntr_bin_reg_3(gnxpm_cdc_rd_pntr_bin_reg_3),
    .E(E),
    .s_axi_wready(s_axi_wready),
    .ram_full_fb_i_reg_0(ram_full_fb_i_reg_0),
    .ram_full_fb_i_reg(ram_full_fb_i_reg),
    .ram_full_fb_i_reg_1(ram_full_fb_i_reg_1)
  );