// SVA for half_full_adder and leaf adders
// Sample after combinational settling using ##0 after any input edge

module half_full_adder_sva (input A, input B, input carry_in, input sum, input carry_out);
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge carry_in or negedge carry_in); endclocking

  // No X/Z on interface
  assert property (##0 !$isunknown({A,B,carry_in,sum,carry_out}));

  // Functional correctness (both canonical forms)
  assert property (##0 (sum == (A ^ B ^ carry_in)));
  assert property (##0 (carry_out == ((A & B) | (B & carry_in) | (A & carry_in))));
  assert property (##0 (carry_out == ((A & B) | ((A ^ B) & carry_in))));

  // Full truth-table coverage (and expected results)
  cover property (##0 (A==0 && B==0 && carry_in==0 && sum==0 && carry_out==0));
  cover property (##0 (A==0 && B==0 && carry_in==1 && sum==1 && carry_out==0));
  cover property (##0 (A==0 && B==1 && carry_in==0 && sum==1 && carry_out==0));
  cover property (##0 (A==0 && B==1 && carry_in==1 && sum==0 && carry_out==1));
  cover property (##0 (A==1 && B==0 && carry_in==0 && sum==1 && carry_out==0));
  cover property (##0 (A==1 && B==0 && carry_in==1 && sum==0 && carry_out==1));
  cover property (##0 (A==1 && B==1 && carry_in==0 && sum==0 && carry_out==1));
  cover property (##0 (A==1 && B==1 && carry_in==1 && sum==1 && carry_out==1));
endmodule

module half_adder_sva (input A, input B, input sum, input carry);
  default clocking cb @(posedge A or negedge A or posedge B or negedge B); endclocking
  assert property (##0 !$isunknown({A,B,sum,carry}));
  assert property (##0 (sum == (A ^ B)));
  assert property (##0 (carry == (A & B)));
  cover property (##0 (A==0 && B==0 && sum==0 && carry==0));
  cover property (##0 (A==0 && B==1 && sum==1 && carry==0));
  cover property (##0 (A==1 && B==0 && sum==1 && carry==0));
  cover property (##0 (A==1 && B==1 && sum==0 && carry==1));
endmodule

module full_adder_sva (input A, input B, input carry_in, input sum, input carry_out);
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge carry_in or negedge carry_in); endclocking
  assert property (##0 !$isunknown({A,B,carry_in,sum,carry_out}));
  assert property (##0 (sum == (A ^ B ^ carry_in)));
  assert property (##0 (carry_out == ((A & B) | (B & carry_in) | (A & carry_in))));
  cover property (##0 (A==0 && B==0 && carry_in==0 && sum==0 && carry_out==0));
  cover property (##0 (A==0 && B==0 && carry_in==1 && sum==1 && carry_out==0));
  cover property (##0 (A==0 && B==1 && carry_in==0 && sum==1 && carry_out==0));
  cover property (##0 (A==0 && B==1 && carry_in==1 && sum==0 && carry_out==1));
  cover property (##0 (A==1 && B==0 && carry_in==0 && sum==1 && carry_out==0));
  cover property (##0 (A==1 && B==0 && carry_in==1 && sum==0 && carry_out==1));
  cover property (##0 (A==1 && B==1 && carry_in==0 && sum==0 && carry_out==1));
  cover property (##0 (A==1 && B==1 && carry_in==1 && sum==1 && carry_out==1));
endmodule

// Bind SVA to DUTs
bind half_full_adder half_full_adder_sva (.*);
bind half_adder      half_adder_sva      (.*);
bind full_adder      full_adder_sva      (.*);