// SVA checker for sky130_fd_sc_hs__o22ai
// Bind this checker to the DUT; provide a clock/reset from your environment.

module sky130_fd_sc_hs__o22ai_sva (
  input logic clk,
  input logic rst_n,
  input logic A1, A2, B1, B2,
  input logic Y
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Derived select and mux output (4-state aware)
  let sel   = (A1 & A2) | (~A1 & ~A2);    // A1 XNOR A2
  let mux_y = sel ? B1 : B2;

  // Core functional correctness (4-state aware)
  a_func:       assert property (Y === mux_y);

  // Known-inputs imply known and correct output
  a_known_out:  assert property (!$isunknown({A1,A2,B1,B2}) |-> (! $isunknown(Y) && (Y == mux_y)));

  // Stability: no input change -> no output change
  a_stable:     assert property ($stable({A1,A2,B1,B2}) |-> $stable(Y));

  // Data-path gating: when sel=1, only B1 can move Y; when sel=0, only B2 can move Y
  a_b1_propag:  assert property ( sel && $stable(A1) && $stable(A2) && $stable(B2) && $changed(B1) |-> $changed(Y) && (Y == B1));
  a_b2_propag:  assert property (!sel && $stable(A1) && $stable(A2) && $stable(B1) && $changed(B2) |-> $changed(Y) && (Y == B2));

  a_b1_blocks:  assert property (!sel && $stable(A1) && $stable(A2) && $stable(B2) && $changed(B1) |-> $stable(Y));
  a_b2_blocks:  assert property ( sel && $stable(A1) && $stable(A2) && $stable(B1) && $changed(B2) |-> $stable(Y));

  // Minimal but meaningful coverage
  c_sel1:       cover  property ( sel);
  c_sel0:       cover  property (!sel);
  c_b1_rise:    cover  property ( sel && $rose(B1));
  c_b1_fall:    cover  property ( sel && $fell(B1));
  c_b2_rise:    cover  property (!sel && $rose(B2));
  c_b2_fall:    cover  property (!sel && $fell(B2));
  c_y_rise:     cover  property ( $rose(Y));
  c_y_fall:     cover  property ( $fell(Y));

endmodule

// Example bind (replace clk/rst_n with your env signals)
// bind sky130_fd_sc_hs__o22ai sky130_fd_sc_hs__o22ai_sva u_o22ai_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));