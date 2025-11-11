// SVA checker for two_input_inv. Bind into the DUT to access internals.
module two_input_inv_sva;

  // Sample on any input edge; use ##0 to allow combinational settle
  default clocking cb @ (posedge a or negedge a or posedge b or negedge b); endclocking

  // Functional equivalence and internal consistency
  ap_func:       assert property (##0 (y === (~a & ~b)));
  ap_not_a:      assert property (##0 (not_a === ~a));
  ap_not_b:      assert property (##0 (not_b === ~b));
  ap_y_from_not: assert property (##0 (y === (not_a & not_b)));
  ap_aandb:      assert property (##0 (a_and_b === (a & b)));

  // Knownness when inputs are known
  ap_known:      assert property ((!$isunknown({a,b})) |-> ##0 (!$isunknown(y)));

  // Output only changes if an input changed
  ap_y_dep:      assert property (@(posedge y or negedge y) ($changed(a) || $changed(b)));

  // Coverage: full truth table and basic toggles
  cp_tt_00:      cover  property (##0 (a==0 && b==0 && y==1));
  cp_tt_01:      cover  property (##0 (a==0 && b==1 && y==0));
  cp_tt_10:      cover  property (##0 (a==1 && b==0 && y==0));
  cp_tt_11:      cover  property (##0 (a==1 && b==1 && y==0));
  cp_y_rise:     cover  property ($rose(y));
  cp_y_fall:     cover  property ($fell(y));
  cp_aandb_tgl:  cover  property ($changed(a_and_b));

endmodule

// Bind into all instances of the DUT
bind two_input_inv two_input_inv_sva sva_inst();