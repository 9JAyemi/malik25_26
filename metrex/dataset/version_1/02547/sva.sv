// SVA for and_gate_with_inverter
// Bind into DUT scope so internal nets are visible
module and_gate_with_inverter_sva;

  // Internal wire correctness
  property p_b1inv;
    @(B1) B1_inv === ~B1;
  endproperty
  assert property (p_b1inv);

  property p_andgate;
    @(A1 or A2 or A3) and_gate_output === (A1 & A2 & A3);
  endproperty
  assert property (p_andgate);

  // Functional equivalence (when all inputs are known)
  property p_func_known;
    @(A1 or A2 or A3 or B1 or C1)
      !$isunknown({A1,A2,A3,B1,C1}) |-> (Y === ((~C1) & (~B1) & A1 & A2 & A3));
  endproperty
  assert property (p_func_known);

  // Strong gating checks (independent of other unknowns as applicable)
  property p_c1_forces_zero;
    @(C1 or Y) (C1 === 1'b1) |-> (Y === 1'b0);
  endproperty
  assert property (p_c1_forces_zero);

  property p_b1_blocks_when_c10;
    @(B1 or C1 or Y) (C1 === 1'b0 && B1 === 1'b1) |-> (Y === 1'b0);
  endproperty
  assert property (p_b1_blocks_when_c10);

  // Optional: power rails sanity (constant in this design)
  initial begin
    assert (VPWR === 1'b1);
    assert (VGND === 1'b0);
  end

  // Coverage: key functional scenarios
  cover property (@(A1 or A2 or A3 or B1 or C1)
                  (C1===1'b0 && B1===1'b0 && A1===1 && A2===1 && A3===1 && Y===1));
  cover property (@(A1 or A2 or A3 or B1 or C1)
                  (C1===1'b1 && Y===1'b0));
  cover property (@(A1 or A2 or A3 or B1 or C1)
                  (C1===1'b0 && B1===1'b1 && Y===1'b0));

  // Toggle coverage for inputs and output
  cover property (@(posedge A1) 1);
  cover property (@(negedge A1) 1);
  cover property (@(posedge A2) 1);
  cover property (@(negedge A2) 1);
  cover property (@(posedge A3) 1);
  cover property (@(negedge A3) 1);
  cover property (@(posedge B1) 1);
  cover property (@(negedge B1) 1);
  cover property (@(posedge C1) 1);
  cover property (@(negedge C1) 1);
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);

endmodule

bind and_gate_with_inverter and_gate_with_inverter_sva sva_inst();