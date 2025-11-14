// SVA for system_auto_cc_0_wr_status_flags_as_16
module system_auto_cc_0_wr_status_flags_as_16_sva (
  input logic                 s_aclk,
  input logic                 out,
  input logic                 s_axi_wvalid,
  input logic [0:0]           Q,
  input logic [0:0]           gnxpm_cdc_rd_pntr_bin_reg_3,
  input logic                 gic0_gc0_count_d1_reg_3,
  input logic [0:0]           E,
  input logic                 s_axi_wready,
  input logic                 ram_full_fb_i_reg,
  input logic                 ram_full_fb_i_reg_0
);
  default clocking cb @(posedge s_aclk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge s_aclk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Combinational equivalences
  assert property (E[0] == (s_axi_wvalid & ram_full_fb_i_reg));
  assert property (ram_full_fb_i_reg_0 == (ram_full_fb_i_reg & s_axi_wvalid & Q[0] & gnxpm_cdc_rd_pntr_bin_reg_3[0]));
  assert property (s_axi_wready == 1'b1);

  // FF behavior
  assert property (out |=> ram_full_fb_i_reg);
  assert property (!out |-> (ram_full_fb_i_reg == $past(gic0_gc0_count_d1_reg_3)));

  // No X/Z on key outputs/state
  assert property (!$isunknown({E[0], s_axi_wready, ram_full_fb_i_reg_0, ram_full_fb_i_reg}));

  // Coverage
  cover property (out ##1 ram_full_fb_i_reg);
  cover property (!out && $rose(gic0_gc0_count_d1_reg_3) ##1 ram_full_fb_i_reg);
  cover property (!out && $fell(gic0_gc0_count_d1_reg_3) ##1 !ram_full_fb_i_reg);
  cover property (s_axi_wvalid && ram_full_fb_i_reg && Q[0] && gnxpm_cdc_rd_pntr_bin_reg_3[0] && E[0] ##0 ram_full_fb_i_reg_0);
endmodule

bind system_auto_cc_0_wr_status_flags_as_16 system_auto_cc_0_wr_status_flags_as_16_sva sva_i (.*);