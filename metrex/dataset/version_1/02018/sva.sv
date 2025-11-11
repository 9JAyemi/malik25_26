// SystemVerilog Assertions for full_adder and ripple_carry_adder

timeunit 1ns/1ps;

// Full adder SVA
module fa_sva;
  // Bound into full_adder; can directly see a,b,cin,sum,cout
  event comb;
  always @* -> comb;

  // Functional correctness
  assert property (@(comb) {cout,sum} == a + b + cin);
  assert property (@(comb) sum == (a ^ b ^ cin));
  assert property (@(comb) cout == ((a & b) | (a & cin) | (b & cin)));

  // No unknowns on outputs when inputs known
  assert property (@(comb) !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout}));

  // Coverage: generate, propagate, kill cases
  cover property (@(comb) (a & b) && cout);                 // generate
  cover property (@(comb) (a ^ b) && cin && cout);          // propagate
  cover property (@(comb) !(a | b) && cin && !cout);        // kill
endmodule

bind full_adder fa_sva fa_sva_i();


// Ripple-carry adder SVA
module rca_sva;
  // Bound into ripple_carry_adder; can directly see a,b,cin,sum,cout,c0..c3
  event comb;
  always @* -> comb;

  // Top-level correctness
  assert property (@(comb) {cout,sum} == a + b + cin);

  // Bit-slice chaining correctness
  assert property (@(comb) {c0,sum[0]} == a[0] + b[0] + cin);
  assert property (@(comb) {c1,sum[1]} == a[1] + b[1] + c0);
  assert property (@(comb) {c2,sum[2]} == a[2] + b[2] + c1);
  assert property (@(comb) {c3,sum[3]} == a[3] + b[3] + c2);
  assert property (@(comb) cout == c3);

  // No unknowns on outputs/internal carries when inputs known
  assert property (@(comb) !$isunknown({a,b,cin}) |-> !$isunknown({sum,cout,c0,c1,c2,c3}));

  // Coverage: overflow, no-overflow, full propagate ripple, all carries set internally
  cover property (@(comb) cout);
  cover property (@(comb) !cout);
  cover property (@(comb) cin && (&(a ^ b)) && ~(|(a & b)) && cout);
  cover property (@(comb) &{c0,c1,c2,c3});
endmodule

bind ripple_carry_adder rca_sva rca_sva_i();