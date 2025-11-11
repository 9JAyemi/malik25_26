// SVA for mux_2to1
module mux_2to1_sva (
  input logic A,
  input logic B,
  input logic SEL,
  input logic Y
);
  // Sample on any input change; use ##0 to avoid preponed-region sampling
  default clocking cb @ (posedge A or negedge A or posedge B or negedge B or posedge SEL or negedge SEL); endclocking

  // Functional correctness (4-state aware)
  a_func:        assert property (##0 (Y === (SEL ? B : A)));

  // Known inputs imply known output
  a_no_x_out:    assert property (##0 ((!$isunknown({A,B,SEL})) |-> !$isunknown(Y)));

  // X-propagation behavior when SEL is unknown
  a_selx_diff:   assert property (##0 (($isunknown(SEL) && (A !== B)) |-> $isunknown(Y)));
  a_selx_same:   assert property (##0 (($isunknown(SEL) && (A === B)) |-> (Y === A)));

  // Minimal functional coverage
  c_sel0_path:   cover  property (##0 (SEL === 1'b0 && Y === A));
  c_sel1_path:   cover  property (##0 (SEL === 1'b1 && Y === B));
  c_y_follows_a: cover  property (##0 (SEL === 1'b0 && $changed(A) ##0 $changed(Y)));
  c_y_follows_b: cover  property (##0 (SEL === 1'b1 && $changed(B) ##0 $changed(Y)));
  c_xprop:       cover  property (##0 ($isunknown(SEL) && (A !== B) && $isunknown(Y)));
endmodule

// Bind into DUT
bind mux_2to1 mux_2to1_sva i_mux_2to1_sva (.A(A), .B(B), .SEL(SEL), .Y(Y));