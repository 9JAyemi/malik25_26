// SVA for ripple_carry_adder and full_adder
// Focused, concise assertions and functional coverage

// Top-level checker bound into ripple_carry_adder (accesses internal carry)
module rca_chk(
  input  logic [3:0] a, b,
  input  logic [3:0] sum,
  input  logic       carry_out,
  input  logic [3:0] carry
);
  // Fire assertions/covers whenever inputs change
  event ev_inputs; always @(a or b) -> ev_inputs;

  // Functional equivalence of the 4-bit ripple adder
  property p_total; !$isunknown({a,b}) |-> ({carry_out,sum} == (a + b)); endproperty
  assert property (@(ev_inputs) p_total);

  // Stage-level correctness (bit-accurate ripple)
  property p_s0; !$isunknown({a[0],b[0]}) |-> ({carry[0],sum[0]} == (a[0] + b[0])); endproperty
  property p_s1; !$isunknown({a[1],b[1],carry[0]}) |-> ({carry[1],sum[1]} == (a[1] + b[1] + carry[0])); endproperty
  property p_s2; !$isunknown({a[2],b[2],carry[1]}) |-> ({carry[2],sum[2]} == (a[2] + b[2] + carry[1])); endproperty
  property p_s3; !$isunknown({a[3],b[3],carry[2]}) |-> ({carry_out,sum[3]} == (a[3] + b[3] + carry[2])); endproperty
  assert property (@(ev_inputs) p_s0);
  assert property (@(ev_inputs) p_s1);
  assert property (@(ev_inputs) p_s2);
  assert property (@(ev_inputs) p_s3);

  // No X/Z on outputs when inputs are known
  property p_known_outs; $isunknown({a,b}) or !$isunknown({sum,carry_out,carry}); endproperty
  assert property (@(ev_inputs) p_known_outs);

  // Targeted functional coverage
  cover property (@(ev_inputs) (a==4'h0 && b==4'h0 && sum==4'h0 && carry_out==1'b0)); // zero + zero
  cover property (@(ev_inputs) (a==4'hF && b==4'hF && sum==4'hE && carry_out==1'b1)); // max + max overflow
  cover property (@(ev_inputs) (carry_out==1'b1));                                    // any overflow
  cover property (@(ev_inputs) (carry[0]));                                           // carry generated at bit0
  cover property (@(ev_inputs) (carry[1]));                                           // carry into bit2
  cover property (@(ev_inputs) (carry[2]));                                           // carry into bit3
  // Ripple propagation chains
  cover property (@(ev_inputs) (a[0]&b[0]) && (a[1]^b[1]) && (carry[1]));             // ripple 1 stage
  cover property (@(ev_inputs) (a[0]&b[0]) && (a[1]^b[1]) && (a[2]^b[2]) && (carry[2])); // ripple 2 stages
  cover property (@(ev_inputs) (a[0]&b[0]) && (a[1]^b[1]) && (a[2]^b[2]) && (a[3]^b[3]) && carry_out); // ripple 3 stages
endmodule

bind ripple_carry_adder rca_chk rca_chk_i(.a(a), .b(b), .sum(sum), .carry_out(carry_out), .carry(carry));


// Checker bound into each full_adder instance
module fa_chk(
  input logic a, b, cin,
  input logic cout, sum
);
  event ev_fa; always @(a or b or cin) -> ev_fa;

  // Equivalence to arithmetic and boolean forms
  property p_fa_add;  !$isunknown({a,b,cin}) |-> ({cout,sum} == (a + b + cin)); endproperty
  property p_fa_bool; !$isunknown({a,b,cin}) |-> (sum == (a ^ b ^ cin) && cout == ((a&b)|(a&cin)|(b&cin))); endproperty
  assert property (@(ev_fa) p_fa_add);
  assert property (@(ev_fa) p_fa_bool);

  // No X/Z on outputs when inputs are known
  property p_fa_known; $isunknown({a,b,cin}) or !$isunknown({sum,cout}); endproperty
  assert property (@(ev_fa) p_fa_known);

  // Basic full-adder functional coverage
  cover property (@(ev_fa) (a&b));               // generate
  cover property (@(ev_fa) (a^b));               // propagate
  cover property (@(ev_fa) (!a && !b));          // kill
  cover property (@(ev_fa) (cin && (a^b)));      // propagate carry-in
  cover property (@(ev_fa) (cin && (a&b)));      // generate irrespective of cin
endmodule

bind full_adder fa_chk fa_chk_i(.a(a), .b(b), .cin(cin), .cout(cout), .sum(sum));