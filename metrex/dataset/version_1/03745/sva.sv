// SVA for three_input_module. Bind into DUT for visibility of internal nets C1/C2.
module three_input_module_sva;
  // Sample on any input change; use ##0 to avoid sampling races.
  default clocking cb @(A1 or A2 or B1); endclocking

  // Core functional correctness (alternative canonical form)
  ap_x_canonical: assert property (1 |-> ##0 (X === (A1 ? ~B1 : (A2 & B1))));

  // Internal net checks
  ap_c1_when_and:  assert property ((A1 & A2)     |-> ##0 (C1 === ~B1));
  ap_c1_else:      assert property ((~(A1 & A2))  |-> ##0 (C1 === (A1 | A2)));
  ap_c2_xor_spec:  assert property (1             |-> ##0 (C2 === (B1 ^ (A1 & A2))));

  // X-propagation: known inputs imply known internals/outputs
  ap_no_x:         assert property (!$isunknown({A1,A2,B1}) |-> ##0 !$isunknown({C1,C2,X}));

  // Functional coverage of all input classes and expected X behavior
  cp_00: cover property ((~A1 & ~A2) |-> ##0 (X === 1'b0));
  cp_01: cover property ((~A1 &  A2) |-> ##0 (X === B1));
  cp_10: cover property (( A1 & ~A2) |-> ##0 (X === ~B1));
  cp_11: cover property (( A1 &  A2) |-> ##0 (X === ~B1));

  // Dynamic behavior on B1 edges under distinct steering conditions
  property p_b1_follow_01;  @(posedge B1 or negedge B1) (~A1 & A2) |-> ##0 (X === B1);  endproperty
  property p_b1_invert_A1;  @(posedge B1 or negedge B1) ( A1      ) |-> ##0 (X === ~B1); endproperty
  cp_b1_follow_01:  cover property (p_b1_follow_01);
  cp_b1_invert_A1:  cover property (p_b1_invert_A1);
endmodule

bind three_input_module three_input_module_sva sva_i();