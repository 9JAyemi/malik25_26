// SVA for and_gate_b1
module and_gate_b1_sva (and_gate_b1 dut);

  // Sample on any input edge
  default clocking cb @(posedge dut.A1 or negedge dut.A1
                      or posedge dut.A2 or negedge dut.A2
                      or posedge dut.A3 or negedge dut.A3
                      or posedge dut.A4 or negedge dut.A4
                      or posedge dut.B1 or negedge dut.B1); endclocking

  // Power rails sanity
  ap_rails_const: assert property (dut.VPWR === 1'b1 && dut.VGND === 1'b0);

  // Functional equivalence when inputs are known (and no X on Y)
  ap_func: assert property (
    !$isunknown({dut.A1,dut.A2,dut.A3,dut.A4,dut.B1})
    |-> ##0 ((dut.Y === (dut.A1 & dut.A2 & dut.A3 & dut.A4 & ~dut.B1)) && !$isunknown(dut.Y))
  );

  // Deterministic low cases
  ap_zero_if_B1_1:   assert property (dut.B1 === 1'b1 |-> ##0 dut.Y === 1'b0);
  ap_zero_if_any_A0: assert property ((dut.A1===1'b0) || (dut.A2===1'b0) || (dut.A3===1'b0) || (dut.A4===1'b0) |-> ##0 dut.Y === 1'b0);

  // High iff all A's are 1 and B1 is 0
  ap_high_when_inputs: assert property ((dut.A1===1'b1 && dut.A2===1'b1 && dut.A3===1'b1 && dut.A4===1'b1 && dut.B1===1'b0) |-> ##0 dut.Y===1'b1);
  ap_high_only_if:     assert property (dut.Y===1'b1 |-> ##0 (dut.A1===1'b1 && dut.A2===1'b1 && dut.A3===1'b1 && dut.A4===1'b1 && dut.B1===1'b0));

  // Coverage
  cp_Y1:       cover property (dut.A1===1'b1 && dut.A2===1'b1 && dut.A3===1'b1 && dut.A4===1'b1 && dut.B1===1'b0 && dut.Y===1'b1);
  cp_B1_masks: cover property (dut.B1===1'b1 && dut.Y===1'b0);
  cp_Y0:       cover property (dut.Y===1'b0);
  cp_Yrise:    cover property ($rose(dut.Y));
  cp_Yfall:    cover property ($fell(dut.Y));
  cp_A1_t:     cover property ($changed(dut.A1));
  cp_A2_t:     cover property ($changed(dut.A2));
  cp_A3_t:     cover property ($changed(dut.A3));
  cp_A4_t:     cover property ($changed(dut.A4));
  cp_B1_t:     cover property ($changed(dut.B1));

endmodule

bind and_gate_b1 and_gate_b1_sva sva_and_gate_b1();