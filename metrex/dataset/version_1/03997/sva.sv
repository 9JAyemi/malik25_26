// Bind these SVA into the DUT
bind my_module my_module_sva sva_inst();

module my_module_sva;

  // Functional correctness (simplified Boolean function)
  ap_func:  assert property (@(*) Y == ~(A1 & B1));

  // Gate-level equivalences
  ap_and0:  assert property (@(*) and0_out   == (A1 & A2));
  ap_and1:  assert property (@(*) and1_out   == (and0_out & B1));
  ap_and2:  assert property (@(*) and2_out   == (A1 & B1));
  ap_nor0:  assert property (@(*) nor0_out_Y == ~(and1_out | and2_out));
  ap_buf0:  assert property (@(*) Y == nor0_out_Y);

  // Redundancy relationship (and1_out implies and2_out)
  ap_impl:  assert property (@(*) and1_out |-> and2_out);

  // A2 does not affect Y (with A1,B1 stable)
  ap_indep: assert property (@(*) !$changed(A1) && !$changed(B1) && $changed(A2) |-> $stable(Y));

  // No X/Z propagation when inputs are known
  ap_no_x:  assert property (@(*) (!$isunknown({A1,A2,B1})) |-> !$isunknown({and0_out,and1_out,and2_out,nor0_out_Y,Y}));

  // Input space coverage (all 8 combinations)
  cp_000: cover property (@(*) {A1,A2,B1} == 3'b000);
  cp_001: cover property (@(*) {A1,A2,B1} == 3'b001);
  cp_010: cover property (@(*) {A1,A2,B1} == 3'b010);
  cp_011: cover property (@(*) {A1,A2,B1} == 3'b011);
  cp_100: cover property (@(*) {A1,A2,B1} == 3'b100);
  cp_101: cover property (@(*) {A1,A2,B1} == 3'b101);
  cp_110: cover property (@(*) {A1,A2,B1} == 3'b110);
  cp_111: cover property (@(*) {A1,A2,B1} == 3'b111);

endmodule