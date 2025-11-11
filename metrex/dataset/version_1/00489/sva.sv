// SVA checker for four_input_and_gate
module four_input_and_gate_sva (
  input logic A1, A2, B1, C1,
  input logic X, W1, W2, W3
);
  // Sample on any relevant activity (combinational checker)
  default clocking cb @(A1 or A2 or B1 or C1 or X or W1 or W2 or W3); endclocking

  // Functional correctness
  a_w1_and:   assert property (W1 === (A1 & A2));
  a_w2_idem:  assert property (W2 === W1);
  a_w3_idem:  assert property (W3 === W2);
  a_x_eq_w3:  assert property (X  === W3);
  a_func_eq:  assert property (X  === (A1 & A2));

  // Unused inputs have no effect on output when real inputs are stable
  a_b1_indep: assert property ( $changed(B1) && $stable({A1,A2}) |=> $stable(X) );
  a_c1_indep: assert property ( $changed(C1) && $stable({A1,A2}) |=> $stable(X) );

  // Functional coverage
  c_00:       cover property (A1==0 && A2==0 && X==0);
  c_01:       cover property (A1==0 && A2==1 && X==0);
  c_10:       cover property (A1==1 && A2==0 && X==0);
  c_11:       cover property (A1==1 && A2==1 && X==1);
  c_rise:     cover property ($rose(X));
  c_fall:     cover property ($fell(X));
  c_b1_tgl:   cover property ($changed(B1) && $stable({A1,A2}) && $stable(X));
  c_c1_tgl:   cover property ($changed(C1) && $stable({A1,A2}) && $stable(X));
endmodule

// Bind into the DUT; .*(name-based) connects ports including internal nets W1/W2/W3
bind four_input_and_gate four_input_and_gate_sva sva_i (.*);