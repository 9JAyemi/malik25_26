// SVA for sky130_fd_sc_lp__inv
// Bind this checker to the DUT; no DUT/testbench edits required.

module sky130_fd_sc_lp__inv_sva (
  input logic A,
  input logic Y,
  input logic not0_out_Y
);

  // Functional: known A implies Y = ~A in same timestep
  ap_func: assert property (@(A or Y) !$isunknown(A) |-> (Y === ~A));

  // X/Z propagation: unknown A implies unknown Y
  ap_xprop: assert property (@(A or Y) $isunknown(A) |-> $isunknown(Y));

  // Internal stage checks
  ap_not:  assert property (@(A or not0_out_Y) !$isunknown(A) |-> (not0_out_Y === ~A));
  ap_buf:  assert property (@(not0_out_Y or Y) (Y === not0_out_Y));
  ap_bufx: assert property (@(not0_out_Y or Y) $isunknown(not0_out_Y) |-> $isunknown(Y));

  // Coverage: exercise both polarities and X-path
  cp_a0y1: cover  property (@(negedge A) (Y == 1));
  cp_a1y0: cover  property (@(posedge A) (Y == 0));
  cp_ax:   cover  property (@(A) $isunknown(A) && $isunknown(Y));

endmodule

bind sky130_fd_sc_lp__inv sky130_fd_sc_lp__inv_sva u_inv_sva (
  .A(A),
  .Y(Y),
  .not0_out_Y(not0_out_Y)
);