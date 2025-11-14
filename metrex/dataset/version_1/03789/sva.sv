// SVA for voltage_supply_circuit
// Bind this file to the DUT; focuses on correctness, dependency, X/Z, and minimal coverage.

module voltage_supply_circuit_sva (
  input logic A1, A2, A3, B1, C1,
  input logic X, X_int,
  input logic VPWR, VGND, VPB, VNB
);

  // Event: sample on any relevant input change
  // (concurrent assertions use this as the clocking event)
  // Note: ##0 used in truth properties to avoid race on same-timestep sampling.

  // Power pins must be correct and constant
  property p_supplies_const;
    @(VPWR or VGND or VPB or VNB)
      (VPWR === 1'b1) and (VPB === 1'b1) and (VGND === 1'b0) and (VNB === 1'b0);
  endproperty
  assert property (p_supplies_const);

  // No X/Z on outputs when driving inputs are known
  property p_outputs_known;
    @(A1 or A2 or A3 or B1 or C1)
      disable iff ($isunknown({A1,A2,A3,B1,C1}))
      !$isunknown({X,X_int});
  endproperty
  assert property (p_outputs_known);

  // Truth checks
  property p_nand2_truth;
    @(B1 or C1 or A1 or A2 or A3) ##0
      disable iff ($isunknown({B1,C1}))
      X === ~(B1 & C1);
  endproperty
  assert property (p_nand2_truth);

  property p_nand3_truth;
    @(A1 or A2 or A3 or B1 or C1) ##0
      disable iff ($isunknown({A1,A2,A3}))
      X_int === ~(A1 & A2 & A3);
  endproperty
  assert property (p_nand3_truth);

  // Dependency checks (outputs change only if their inputs change)
  property p_X_change_implies_B_change;
    @(A1 or A2 or A3 or B1 or C1)
      $changed(X) |-> $changed({B1,C1});
  endproperty
  assert property (p_X_change_implies_B_change);

  property p_Xint_change_implies_A_change;
    @(A1 or A2 or A3 or B1 or C1)
      $changed(X_int) |-> $changed({A1,A2,A3});
  endproperty
  assert property (p_Xint_change_implies_A_change);

  // Minimal but meaningful coverage
  cover property (@(B1 or C1 or A1 or A2 or A3) B1 && C1 ##0 (X===1'b0));
  cover property (@(B1 or C1 or A1 or A2 or A3) B1 && !C1 ##0 (X===1'b1));
  cover property (@(B1 or C1 or A1 or A2 or A3) !B1 && C1 ##0 (X===1'b1));

  cover property (@(A1 or A2 or A3 or B1 or C1)  A1 && A2 && A3 ##0 (X_int===1'b0));
  cover property (@(A1 or A2 or A3 or B1 or C1) !(A1 && A2 && A3) ##0 (X_int===1'b1));

  cover property (@(A1 or A2 or A3 or B1 or C1) $rose(X));
  cover property (@(A1 or A2 or A3 or B1 or C1) $fell(X));
  cover property (@(A1 or A2 or A3 or B1 or C1) $rose(X_int));
  cover property (@(A1 or A2 or A3 or B1 or C1) $fell(X_int));

endmodule

// Bind into the DUT, including internal net X_int and supplies
bind voltage_supply_circuit voltage_supply_circuit_sva sva_i (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .C1(C1),
  .X(X), .X_int(X_int),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);