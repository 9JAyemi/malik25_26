// SVA checker for inverter_gate
// Focus: concise, high-quality functional checks + coverage
module inverter_gate_sva (
    input  A,
    input  Z,
    input  TE,
    input  VPB,
    input  VPWR,
    input  VGND,
    input  VNB,
    input  inv_A
);

  // Functional correctness (core truth table)
  property p_func; @(*) Z === (TE ? ~A : VNB); endproperty
  assert property (p_func) else $error("Z != (TE ? ~A : VNB)");

  // Internal inversion correctness
  property p_inv;  @(*) inv_A === ~A; endproperty
  assert property (p_inv) else $error("inv_A != ~A");

  // No high-Z on output
  assert property (@(*) Z !== 1'bz) else $error("Z is Z");

  // If inputs are known, output must be known and correct
  property p_no_x_when_inputs_known;
    @(*) (!$isunknown({A,TE,VNB})) |-> (Z == (TE ? ~A : VNB));
  endproperty
  assert property (p_no_x_when_inputs_known) else $error("Z unknown/mismatch with known inputs");

  // Well/power tie sanity (common physical expectation)
  assert property (@(*) (VPB === VPWR) && (VNB === VGND))
    else $error("Well ties not matching supplies (VPB!=VPWR or VNB!=VGND)");

  // Output stability when inputs stable
  property p_stable;
    @(*) $stable({A,TE,VNB}) |-> $stable(Z);
  endproperty
  assert property (p_stable) else $error("Z changed without input change");

  // Mode-specific refinements (redundant to p_func but localizes debug)
  assert property (@(*)  TE |-> (Z === ~A)) else $error("TE=1: Z != ~A");
  assert property (@(*) !TE |-> (Z === VNB)) else $error("TE=0: Z != VNB");

  // Coverage: exercise both modes and transitions
  cover property (@(posedge A)  TE && (Z === ~A));
  cover property (@(negedge A)  TE && (Z === ~A));
  cover property (@(posedge VNB) !TE && (Z === VNB));
  cover property (@(negedge VNB)!TE && (Z === VNB));
  cover property (@(posedge TE)  (Z === ~A));
  cover property (@(negedge TE)  (Z === VNB));

  // Cross-state coverage of key combinations (concise)
  cover property (@(*) TE && (A==0) && (Z===1));
  cover property (@(*) TE && (A==1) && (Z===0));
  cover property (@(*) !TE && (VNB==0) && (Z===0));
  cover property (@(*) !TE && (VNB==1) && (Z===1));

endmodule

// Bind into DUT (captures internal inv_A as well)
bind inverter_gate inverter_gate_sva u_inverter_gate_sva (
  .A(A), .Z(Z), .TE(TE), .VPB(VPB), .VPWR(VPWR), .VGND(VGND), .VNB(VNB), .inv_A(inv_A)
);