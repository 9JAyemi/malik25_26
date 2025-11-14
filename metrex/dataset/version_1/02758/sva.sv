// SVA checker for MUX. Bind this module to your MUX instance.
// Example bind (hook clk/rst_n from your TB):
// bind MUX MUX_sva u_mux_sva(.clk(tb_clk), .rst_n(tb_rst_n), .in0(in0), .in1(in1), .in2(in2), .in3(in3), .sel0(sel0), .sel1(sel1), .out(out));

module MUX_sva (
  input logic clk,
  input logic rst_n,
  input logic in0, in1, in2, in3,
  input logic sel0, sel1,
  input logic out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Local decode (mirrors DUT intent)
  logic sel_00 = ~(sel0 | sel1);
  logic sel_01 = ~sel0 & sel1;
  logic sel_10 = sel0 & ~sel1;
  logic sel_11 = sel0 & sel1;

  // Functional equivalence (truth table in one assertion)
  a_func: assert property (out == ((sel_00 & in0) | (sel_01 & in1) | (sel_10 & in2) | (sel_11 & in3)));

  // Decode is one-hot across all 4 cases
  a_onehot: assert property ($onehot({sel_00, sel_01, sel_10, sel_11}));

  // No X/Z on out when inputs/selects are known
  a_no_x: assert property (!$isunknown({sel0,sel1,in0,in1,in2,in3}) |-> !$isunknown(out));

  // No spurious glitches: if all drivers are stable across a cycle, out is stable
  a_stable: assert property ($stable({sel0,sel1,in0,in1,in2,in3}) |-> $stable(out));

  // Coverage: hit all select combinations
  c_sel00: cover property (sel_00);
  c_sel01: cover property (sel_01);
  c_sel10: cover property (sel_10);
  c_sel11: cover property (sel_11);

  // Coverage: selected input toggle propagates to out
  c_prop0: cover property (sel_00 && $past(sel_00) && $changed(in0) && $changed(out));
  c_prop1: cover property (sel_01 && $past(sel_01) && $changed(in1) && $changed(out));
  c_prop2: cover property (sel_10 && $past(sel_10) && $changed(in2) && $changed(out));
  c_prop3: cover property (sel_11 && $past(sel_11) && $changed(in3) && $changed(out));

endmodule