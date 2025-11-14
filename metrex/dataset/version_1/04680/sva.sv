// SVA for sky130_fd_sc_ls__clkdlyinv5sd2
// Function: Y = ~A (with X/Z propagation)

module sky130_fd_sc_ls__clkdlyinv5sd2_sva (
  input logic A,
  input logic Y
);

  // Sample on any edge of A or Y
  default clocking cb @(posedge A or negedge A or posedge Y or negedge Y); endclocking

  // Functional correctness (includes X/Z propagation)
  a_func_inv:     assert property (Y === ~A);

  // Explicit 0/1 cases
  a_a0_y1:        assert property ((A === 1'b0) |-> (Y === 1'b1));
  a_a1_y0:        assert property ((A === 1'b1) |-> (Y === 1'b0));

  // X/Z on input must propagate to output
  a_xprop:        assert property ($isunknown(A) |-> $isunknown(Y));

  // Polarity of transitions (only for known edges)
  a_rise_fall:    assert property ($rose(A) |-> $fell(Y));
  a_fall_rise:    assert property ($fell(A) |-> $rose(Y));

  // Coverage: values, transitions, and X-propagation
  c_a0y1:         cover  property (A === 1'b0 && Y === 1'b1);
  c_a1y0:         cover  property (A === 1'b1 && Y === 1'b0);
  c_rise_fall:    cover  property ($rose(A) && $fell(Y));
  c_fall_rise:    cover  property ($fell(A) && $rose(Y));
  c_xprop:        cover  property ($isunknown(A) && $isunknown(Y));

endmodule

// Bind into DUT
bind sky130_fd_sc_ls__clkdlyinv5sd2 sky130_fd_sc_ls__clkdlyinv5sd2_sva sva_i (.A(A), .Y(Y));