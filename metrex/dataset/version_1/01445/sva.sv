// SVA checker for full_adder
module full_adder_sva;
  // Sample on any relevant signal activity to catch comb updates
  default clocking cb @(
      A or B or Ci or S or Co or
      n1 or n2 or n3 or n4 or n5 or n6 or n7 or n8 or n9 or n10 or n11
  ); endclocking

  // Known outputs when inputs are known
  ap_known_outs: assert property ( !$isunknown({A,B,Ci}) |-> ##0 !$isunknown({S,Co}) );

  // Black-box functional spec
  ap_sum_spec:   assert property ( !$isunknown({A,B,Ci}) |-> ##0 ( S  === (A ^ B ^ Ci) ) );
  ap_carry_spec: assert property ( !$isunknown({A,B,Ci}) |-> ##0 ( Co === ((A & B) | (A & Ci) | (B & Ci)) ) );

  // White-box structural checks (as coded)
  ap_n11: assert property ( ##0 n11 === ~(A ^ B) );
  ap_S_eq: assert property ( ##0  S === ~(Ci ^ n11) );
  ap_n10: assert property ( ##0 n10 === ~(A & B & Ci) );
  ap_n9:  assert property ( ##0 n9  === ~(A & B) );
  ap_Co_eq: assert property ( ##0 Co === ~(n10 & n9) );
  ap_n1:  assert property ( ##0 n1 === ~(Ci & n11) );
  ap_n2:  assert property ( ##0 n2 === ~(B  & n11) );
  ap_n3:  assert property ( ##0 n3 === ~(A  & Ci) );
  ap_n4:  assert property ( ##0 n4 === ~(n1 & n2) );
  ap_n5:  assert property ( ##0 n5 === ~(n3 & n9) );
  ap_n6:  assert property ( ##0 n6 === ~(n3 & n2) );
  ap_n7:  assert property ( ##0 n7 === ~(n1 & n9) );
  ap_n8:  assert property ( ##0 n8 === ~(n6 & n7) );

  // Functional coverage of all input combinations (and expected outputs)
  cover_000: cover property ( (A==0 && B==0 && Ci==0) ##0 (S==0 && Co==0) );
  cover_001: cover property ( (A==0 && B==0 && Ci==1) ##0 (S==1 && Co==0) );
  cover_010: cover property ( (A==0 && B==1 && Ci==0) ##0 (S==1 && Co==0) );
  cover_011: cover property ( (A==0 && B==1 && Ci==1) ##0 (S==0 && Co==1) );
  cover_100: cover property ( (A==1 && B==0 && Ci==0) ##0 (S==1 && Co==0) );
  cover_101: cover property ( (A==1 && B==0 && Ci==1) ##0 (S==0 && Co==1) );
  cover_110: cover property ( (A==1 && B==1 && Ci==0) ##0 (S==0 && Co==1) );
  cover_111: cover property ( (A==1 && B==1 && Ci==1) ##0 (S==1 && Co==1) );
endmodule

// Bind into the DUT
bind full_adder full_adder_sva sva_inst();