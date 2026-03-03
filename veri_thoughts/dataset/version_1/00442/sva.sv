// SVA for tap_point
// Bind into DUT to check/cover function concisely

module tap_point_sva (
  input logic vin,
  input logic gnd,
  input logic tap,
  input logic vin_gnd
);

  // Sample on any input edge; use ##0 to evaluate after combinational settle
  default clocking cb @(posedge vin or negedge vin or posedge gnd or negedge gnd); endclocking

  // Functional equivalence when inputs are 2-state
  property p_func_2state;
    !$isunknown({vin,gnd}) |-> ##0 (tap === vin);
  endproperty
  assert property (p_func_2state);

  // When inputs are equal (including X===X), tap equals them
  property p_equal_branch;
    (vin === gnd) |-> ##0 (tap === vin);
  endproperty
  assert property (p_equal_branch);

  // True-branch behavior when inputs differ and are 2-state
  property p_true_branch;
    (!$isunknown({vin,gnd}) && (vin != gnd)) |-> ##0 (tap == vin);
  endproperty
  assert property (p_true_branch);

  // Internal net matches 1-bit XOR of inputs when 2-state
  property p_vin_gnd_is_xor;
    !$isunknown({vin,gnd}) |-> ##0 (vin_gnd === (vin ^ gnd));
  endproperty
  assert property (p_vin_gnd_is_xor);

  // No spurious tap change without an input change
  property p_no_spurious_tap_change;
    @(posedge tap or negedge tap) 1 |-> ($changed(vin) || $changed(gnd));
  endproperty
  assert property (p_no_spurious_tap_change);

  // Coverage: both mux paths and all input combos
  cover property (##0 (!$isunknown({vin,gnd}) && (vin==0) && (gnd==0)));
  cover property (##0 (!$isunknown({vin,gnd}) && (vin==0) && (gnd==1)));
  cover property (##0 (!$isunknown({vin,gnd}) && (vin==1) && (gnd==0)));
  cover property (##0 (!$isunknown({vin,gnd}) && (vin==1) && (gnd==1)));

  cover property (##0 (!$isunknown({vin,gnd}) && (vin!=gnd) && (tap==vin))); // true branch
  cover property (##0 (vin===gnd) && (tap===vin));                           // false/equal branch

  // Coverage: X-propagation scenarios observed
  cover property (##0 (($isunknown(vin) || $isunknown(gnd)) && $isunknown(tap)));

endmodule

// Bind into all instances of tap_point (vin_gnd is internal net)
bind tap_point tap_point_sva sva_i (
  .vin(vin),
  .gnd(gnd),
  .tap(tap),
  .vin_gnd(vin_gnd)
);