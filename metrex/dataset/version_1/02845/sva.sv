// SVA for the full_adder, four_bit_adder, and top_module.
// Focused, concise checks with key functional coverage.

module full_adder_sva (input a, b, cin, sum, cout);
  default clocking cb @(a or b or cin); endclocking

  // Inputs known -> outputs known and correct
  property fa_func;
    !$isunknown({a,b,cin}) |-> ##0
      (! $isunknown({sum,cout}) &&
       sum == (a ^ b ^ cin) &&
       cout == ((a & b) | (a & cin) | (b & cin)));
  endproperty
  assert property (fa_func);

  // Truth-table coverage for all 8 input combinations
  cover property (##0 {a,b,cin} == 3'b000);
  cover property (##0 {a,b,cin} == 3'b001);
  cover property (##0 {a,b,cin} == 3'b010);
  cover property (##0 {a,b,cin} == 3'b011);
  cover property (##0 {a,b,cin} == 3'b100);
  cover property (##0 {a,b,cin} == 3'b101);
  cover property (##0 {a,b,cin} == 3'b110);
  cover property (##0 {a,b,cin} == 3'b111);
endmodule

module four_bit_adder_sva (
  input [3:0] a, b,
  input [3:0] sum,
  input       cout,
  input [2:0] c // internal carries
);
  default clocking cb @(a or b); endclocking

  // Inputs known -> all outputs/carries known and correct total sum
  property add_total_ok;
    !$isunknown({a,b}) |-> ##0
      (! $isunknown({sum,cout,c}) &&
       {cout,sum} == ({1'b0,a} + {1'b0,b}));
  endproperty
  assert property (add_total_ok);

  // Internal carry chain correctness (cin to bit0 is 0)
  assert property (##0 c[0] == (a[0] & b[0]));
  assert property (##0 c[1] == ((a[1] & b[1]) | ((a[1]^b[1]) & c[0])));
  assert property (##0 c[2] == ((a[2] & b[2]) | ((a[2]^b[2]) & c[1])));

  // Optional sum-bit checks against local carries (redundant but pinpointing)
  assert property (##0 sum[0] == (a[0]^b[0]));
  assert property (##0 sum[1] == (a[1]^b[1]^c[0]));
  assert property (##0 sum[2] == (a[2]^b[2]^c[1]));
  assert property (##0 sum[3] == (a[3]^b[3]^c[2]));

  // Coverage of key ripple-carry scenarios
  cover property (##0 cout == 0);
  cover property (##0 cout == 1);
  // Longest ripple: generate @bit0, propagate through bits 1..3
  cover property (##0 (a[0]&b[0]) && &(a[3:1]^b[3:1]) && cout);
  // Generate @bit1, propagate through 2..3
  cover property (##0 (a[1]&b[1]) && &(a[3:2]^b[3:2]) && ! (a[0]&b[0]) && cout);
  // Generate @bit2, propagate through 3
  cover property (##0 (a[2]&b[2]) && (a[3]^b[3]) && !(a[1]&b[1]) && !(a[0]&b[0]) && cout);
  // Generate @bit3 (immediate carry-out)
  cover property (##0 (a[3]&b[3]) && cout);
  // All-propagate, no generate, no carry-out
  cover property (##0 (&(a^b)) && ~(|(a & b)) && (cout==0));
endmodule

module top_module_sva (
  input [3:0] a, b,
  input [4:0] sum
);
  default clocking cb @(a or b); endclocking

  // Top-level: inputs known -> sum known and exactly a+b
  property top_sum_ok;
    !$isunknown({a,b}) |-> ##0
      (! $isunknown(sum) &&
       sum == ({1'b0,a} + {1'b0,b}));
  endproperty
  assert property (top_sum_ok);

  // Coverage for carry-out 0/1 and extremes
  cover property (##0 sum[4]==0);
  cover property (##0 sum[4]==1);
  cover property (##0 sum == 5'd0);
  cover property (##0 sum == 5'd30); // 15 + 15
endmodule

// Bind checkers to DUTs
bind full_adder      full_adder_sva      u_full_adder_sva      (.*);
bind four_bit_adder  four_bit_adder_sva  u_four_bit_adder_sva  (.*);
bind top_module      top_module_sva      u_top_module_sva      (.*);