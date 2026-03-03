// SVA checker for mux4to1_enable
// Bind this to the DUT and provide a clock/reset from your environment.

module mux4to1_enable_sva (
  input logic         clk,
  input logic         rst_n,
  input logic  [3:0]  in,
  input logic         en,
  input logic         out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional correctness (the nested ternary reduces to en ? in[0] : in[3])
  assert property (out == (en ? in[0] : in[3]))
    else $error("mux4to1_enable: out != (en?in[0]:in[3]) en=%0b in=%0b out=%0b", en, in, out);

  // X-propagation sanity: no unknowns on control/output; selected data must be known
  assert property (!$isunknown(en)) else $error("mux4to1_enable: en is X/Z");
  assert property (!$isunknown(out)) else $error("mux4to1_enable: out is X/Z");
  assert property (en  |-> !$isunknown(in[0])) else $error("mux4to1_enable: in[0] X/Z when selected");
  assert property (!en |-> !$isunknown(in[3])) else $error("mux4to1_enable: in[3] X/Z when selected");

  // Independence checks: in[1] and in[2] do not affect out (exposes dead selects)
  assert property ($changed(in[1]) && $stable(en) && $stable(in[0]) && $stable(in[3]) |-> $stable(out))
    else $error("mux4to1_enable: out changed due to in[1]");
  assert property ($changed(in[2]) && $stable(en) && $stable(in[0]) && $stable(in[3]) |-> $stable(out))
    else $error("mux4to1_enable: out changed due to in[2]");

  // Coverage: exercise both selections and observe redundancy of in[1]/in[2]
  cover property (en && out == in[0]);
  cover property (!en && out == in[3]);
  cover property ($changed(in[1]) && $stable(out));
  cover property ($changed(in[2]) && $stable(out));
  cover property ($changed(out));
endmodule

// Bind example (connect clk/rst from your TB/env)
// bind mux4to1_enable mux4to1_enable_sva u_mux4to1_enable_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));