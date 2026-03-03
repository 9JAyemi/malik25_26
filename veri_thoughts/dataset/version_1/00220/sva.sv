// SVA for synchronizer_ff_15
module synchronizer_ff_15_sva (
  input logic         s_axi_aclk,
  input logic  [0:0]  in0,
  input logic         out,
  input logic         rd_rst_asreg_reg
);

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge s_axi_aclk) past_valid <= 1'b1;

  default clocking cb @(posedge s_axi_aclk); endclocking
  default disable iff (!past_valid);

  // No Xs on sampled interface signals
  assert property (!$isunknown({in0[0], out, rd_rst_asreg_reg}));

  // Combinational reset definition matches spec: rd_rst_asreg_reg == (in0 != prev out)
  assert property (rd_rst_asreg_reg == (in0[0] != $past(out)));

  // Same-cycle (post-NBA) behavior: next out = (in0 != prev out) ? 0 : in0
  assert property (1'b1 |-> ##0 (out == ((in0[0] != $past(out)) ? 1'b0 : in0[0])));

  // If reset branch taken at edge, out must be driven low in the same cycle
  assert property (rd_rst_asreg_reg |-> ##0 (out == 1'b0));

  // Coverage: see both branches and both stable input values
  cover property (in0[0] != $past(out));             // mismatch -> reset path exercised
  cover property (in0[0] == $past(out) && in0[0]);   // match with 1
  cover property (in0[0] == $past(out) && !in0[0]);  // match with 0

endmodule

bind synchronizer_ff_15 synchronizer_ff_15_sva sva_i (
  .s_axi_aclk(s_axi_aclk),
  .in0(in0),
  .out(out),
  .rd_rst_asreg_reg(rd_rst_asreg_reg)
);