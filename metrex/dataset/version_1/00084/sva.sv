// SVA for input_interface
// Focus: functional equivalence of X, independence from A/SLEEP/VPWR/VPB,
// X-propagation, and basic coverage.

// Bindable checker module
module input_interface_sva (
  input logic A,
  input logic SLEEP,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic X
);

  // Functional: X must equal pass-through/invert of VNB selected by VGND.
  // Use 4-state equality and ##0 to avoid delta-cycle races.
  property p_func;
    @(A or SLEEP or VPWR or VGND or VPB or VNB)
      ##0 (X === ((VGND === 1'b1) ? ~VNB : VNB));
  endproperty
  assert property (p_func);

  // Irrelevant inputs must not affect X (A, SLEEP, VPWR, VPB changes alone).
  property p_irrelevant_changes_do_not_affect_X;
    @(A or SLEEP or VPWR or VPB or VGND or VNB)
      ($changed({A,SLEEP,VPWR,VPB}) && $stable({VGND,VNB})) |-> ##0 $stable(X);
  endproperty
  assert property (p_irrelevant_changes_do_not_affect_X);

  // X must flip when VGND toggles with VNB stable and both known.
  property p_vgnd_toggle_flips_X;
    @(VGND or VNB)
      ($changed(VGND) && $stable(VNB) && !$isunknown({VGND,VNB})) |-> ##0 (X == ~$past(X));
  endproperty
  assert property (p_vgnd_toggle_flips_X);

  // X must flip when VNB toggles with VGND stable and both known.
  property p_vnb_toggle_flips_X;
    @(VGND or VNB)
      ($changed(VNB) && $stable(VGND) && !$isunknown({VGND,VNB})) |-> ##0 (X == ~$past(X));
  endproperty
  assert property (p_vnb_toggle_flips_X);

  // If all inputs are known, X shall be known (no unintended X/Z propagation).
  property p_no_unknown_when_inputs_known;
    @(A or SLEEP or VPWR or VGND or VPB or VNB)
      (!$isunknown({A,SLEEP,VPWR,VGND,VPB,VNB})) |-> ##0 !$isunknown(X);
  endproperty
  assert property (p_no_unknown_when_inputs_known);

  // Coverage: exercise both VGND modes and X activity from VNB changes.
  cover property (@(VGND or VNB) (VGND===1'b0 && !$isunknown(VNB)) ##0 (X===VNB));
  cover property (@(VGND or VNB) (VGND===1'b1 && !$isunknown(VNB)) ##0 (X===~VNB));

  cover property (@(VNB) (VGND===1'b0 && $changed(VNB) && !$isunknown(VNB)) ##0 $changed(X));
  cover property (@(VNB) (VGND===1'b1 && $changed(VNB) && !$isunknown(VNB)) ##0 $changed(X));

  // Coverage: irrelevant controls toggled while X remains stable.
  cover property (@(A or SLEEP or VPWR or VPB)
                  $changed({A,SLEEP,VPWR,VPB}) && $stable({VGND,VNB}) ##0 $stable(X));

endmodule

// Bind into DUT
bind input_interface input_interface_sva i_input_interface_sva (
  .A(A), .SLEEP(SLEEP), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .X(X)
);