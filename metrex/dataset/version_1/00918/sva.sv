// SVA checkers + binds for full_adder and ripple_adder

// Full-adder checker
module full_adder_sva(
  input a, b, carry_in,
  input sum, carry_out
);
  // Functional correctness (math and logic forms) and X-safety
  assert property (@(a or b or carry_in or sum or carry_out)
                   !$isunknown({a,b,carry_in}) |-> ##0 ({carry_out,sum} == a + b + carry_in));
  assert property (@(a or b or carry_in or sum or carry_out)
                   !$isunknown({a,b,carry_in}) |-> ##0 (sum == (a ^ b) ^ carry_in));
  assert property (@(a or b or carry_in or sum or carry_out)
                   !$isunknown({a,b,carry_in}) |-> ##0 (carry_out == (a & b) | (a & carry_in) | (b & carry_in)));
  assert property (@(a or b or carry_in or sum or carry_out)
                   !$isunknown({a,b,carry_in}) |-> ##0 !$isunknown({sum,carry_out}));

  // Full input space coverage (8 combinations)
  cover property (@(a or b or carry_in) {a,b,carry_in} == 3'b000);
  cover property (@(a or b or carry_in) {a,b,carry_in} == 3'b001);
  cover property (@(a or b or carry_in) {a,b,carry_in} == 3'b010);
  cover property (@(a or b or carry_in) {a,b,carry_in} == 3'b011);
  cover property (@(a or b or carry_in) {a,b,carry_in} == 3'b100);
  cover property (@(a or b or carry_in) {a,b,carry_in} == 3'b101);
  cover property (@(a or b or carry_in) {a,b,carry_in} == 3'b110);
  cover property (@(a or b or carry_in) {a,b,carry_in} == 3'b111);
endmodule

bind full_adder full_adder_sva (.a(a), .b(b), .carry_in(carry_in), .sum(sum), .carry_out(carry_out));



// Ripple-carry adder checker
module ripple_adder_sva(
  input [3:0] a, b, sum,
  input       cin, cout,
  input [3:0] carry   // bound to DUT internal carry bus
);
  // End-to-end arithmetic correctness and X-safety
  assert property (@(a or b or cin or sum or cout)
                   !$isunknown({a,b,cin}) |-> ##0 ({cout,sum} == a + b + cin));
  assert property (@(a or b or cin or sum or cout or carry)
                   !$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout}));

  // Bitwise sum checks (carry-in per stage)
  assert property (@(a or b or cin or sum) !$isunknown({a[0],b[0],cin}) |-> ##0 (sum[0] == (a[0]^b[0]) ^ cin));
  assert property (@(a or b or carry or sum) !$isunknown({a[1],b[1],carry[0]}) |-> ##0 (sum[1] == (a[1]^b[1]) ^ carry[0]));
  assert property (@(a or b or carry or sum) !$isunknown({a[2],b[2],carry[1]}) |-> ##0 (sum[2] == (a[2]^b[2]) ^ carry[1]));
  assert property (@(a or b or carry or sum) !$isunknown({a[3],b[3],carry[2]}) |-> ##0 (sum[3] == (a[3]^b[3]) ^ carry[2]));

  // Carry chain correctness (majority function per stage)
  assert property (@(a or b or cin or carry) !$isunknown({a[0],b[0],cin}) |-> ##0
                   (carry[0] == (a[0]&b[0]) | (a[0]&cin) | (b[0]&cin)));
  assert property (@(a or b or carry) !$isunknown({a[1],b[1],carry[0]}) |-> ##0
                   (carry[1] == (a[1]&b[1]) | (a[1]&carry[0]) | (b[1]&carry[0])));
  assert property (@(a or b or carry) !$isunknown({a[2],b[2],carry[1]}) |-> ##0
                   (carry[2] == (a[2]&b[2]) | (a[2]&carry[1]) | (b[2]&carry[1])));
  assert property (@(a or b or carry or cout) !$isunknown({a[3],b[3],carry[2]}) |-> ##0
                   (cout == (a[3]&b[3]) | (a[3]&carry[2]) | (b[3]&carry[2])));

  // Additional X-safety on internal carry when inputs are known
  assert property (@(a or b or cin or carry) !$isunknown({a,b,cin}) |-> ##0 !$isunknown(carry[2:0]));

  // Targeted coverage of critical behaviors
  // No-carry addition
  cover property (@(a or b or cin) (a==4'h0 && b==4'h0 && cin==1'b0 && cout==0 && sum==4'h0));
  // Overflow
  cover property (@(a or b or cin) (a==4'hF && b==4'hF && cin==1'b1 && cout==1));
  // Full propagate chain (all bits propagate a^b==4'hF) with cin ripple-through
  cover property (@(a or b or cin or cout) ((a^b)==4'hF && cin==1 && cout==1));
  // MSB generate producing cout independent of propagate
  cover property (@(a or b or cin or cout or carry) (a[3]&b[3] && carry[2]==0 && cout==1));
endmodule

bind ripple_adder ripple_adder_sva (.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout), .carry(carry));