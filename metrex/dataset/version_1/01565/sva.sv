// SVA for d_ff: concise, high-quality checks and coverage
`ifndef D_FF_SVA
`define D_FF_SVA

module d_ff_sva (
  input  Q,
  input  Q_N,
  input  CLK,
  input  D,
  input  VPWR,
  input  VGND,
  input  VPB,
  input  VNB
);

  // Power-good gating
  wire pwr_good = (VPWR===1'b1 && VGND===1'b0);

  // Past-valid for cycle-accurate checks
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!pwr_good || !past_valid);

  // Outputs must be known when powered
  assert property (!$isunknown({Q,Q_N}));

  // Bulk/reset pins should be known when powered
  assert property (!$isunknown({VPB,VNB}));

  // Q_N is always the complement of Q
  assert property (Q_N == ~Q);

  // Functional behavior: on each rising edge, Q captures D unless reset low
  assert property (Q == (($past(VPB)==1'b0) ? 1'b0 : $past(D)));

  // Q changes only on CLK rising edge (no glitches)
  assert property (disable iff (!pwr_good) $changed(Q) |-> $rose(CLK));

  // D must be known when sampled (when not in reset)
  assert property (VPB==1'b1 |-> !$isunknown(D));

  // Coverage: capture both 0 and 1, reset action, and toggles
  cover property (VPB==1'b1 && D==0 ##1 Q==0);
  cover property (VPB==1'b1 && D==1 ##1 Q==1);
  cover property (VPB==1'b0 ##1 Q==0);
  cover property ($past(Q)==0 && Q==1);
  cover property ($past(Q)==1 && Q==0);

endmodule

bind d_ff d_ff_sva sva_d_ff (.*);

`endif