// Bindable SVA checker for adder4
module adder4_sva;
  // This module is bound into adder4; it can see a, b, cin, sum, cout, and internal carry[3:1]
  default clocking cb @(a or b or cin); endclocking

  // Reusable guard: only check when inputs are known; sample results after settling (##0)
  sequence clean_in; !$isunknown({a,b,cin}); endsequence

  // No X on outputs if inputs are clean
  ap_no_x:   assert property (clean_in |-> ##0 !$isunknown({sum,cout}));

  // Arithmetic equivalence for the whole adder
  ap_arith:  assert property (clean_in |-> ##0 {cout, sum} == a + b + cin);

  // Structural bit/carry equations
  ap_s0:     assert property (clean_in |-> ##0 (sum[0] == (a[0] ^ b[0] ^ cin)));
  ap_c1:     assert property (clean_in |-> ##0 (carry[1] == ((a[0] & b[0]) | (cin & (a[0] ^ b[0])))));
  ap_s1:     assert property (clean_in |-> ##0 (sum[1] == (a[1] ^ b[1] ^ carry[1])));
  ap_c2:     assert property (clean_in |-> ##0 (carry[2] == ((a[1] & b[1]) | (carry[1] & (a[1] ^ b[1])))));
  ap_s2:     assert property (clean_in |-> ##0 (sum[2] == (a[2] ^ b[2] ^ carry[2])));
  ap_c3:     assert property (clean_in |-> ##0 (carry[3] == ((a[2] & b[2]) | (carry[2] & (a[2] ^ b[2])))));
  ap_s3:     assert property (clean_in |-> ##0 (sum[3] == (a[3] ^ b[3] ^ carry[3])));
  ap_cout:   assert property (clean_in |-> ##0 (cout    == ((a[3] & b[3]) | (carry[3] & (a[3] ^ b[3])))));

  // Functional coverage (key scenarios)
  cp_seen:         cover property (clean_in ##0 ({cout, sum} == a + b + cin));

  // Full propagate chain: cin ripples through all stages (sum=0, cout=1)
  cp_full_ripple:  cover property (clean_in and cin and ((a ^ b) == 4'hF) and ((a & b) == 4'h0)
                                   ##0 (sum == 4'h0 && cout));

  // Zero add
  cp_zero:         cover property ((a==4'h0) && (b==4'h0) && !cin ##0 (sum==4'h0 && !cout));

  // Max overflow: 15+15+1 = 31
  cp_overflow:     cover property ((a==4'hF) && (b==4'hF) && cin ##0 ({cout,sum}==5'h1F));

  // Hit each internal carry and final carry at least once
  cp_c1:           cover property (carry[1]);
  cp_c2:           cover property (carry[2]);
  cp_c3:           cover property (carry[3]);
  cp_co:           cover property (cout);
endmodule

// Bind into all instances of adder4
bind adder4 adder4_sva sva_i();