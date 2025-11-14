// SVA for half_adder_nand
module half_adder_nand_sva(
  input logic a, b,
  input logic sum, cout,
  input logic s1, s2, c1
);

  // Spec: sum = a ^ b, cout = a & b (combinational, allow delta settle)
  assert property (@(a or b) !$isunknown({a,b}) |-> ##0 (sum == (a ^ b) && cout == (a & b)));

  // Structural NAND checks
  assert property (@(a or b) !$isunknown({a,b}) |-> ##0 (s1 == ~(a & b)));
  assert property (@(a or s1) !$isunknown({a,s1}) |-> ##0 (s2 == ~(a & s1)));
  assert property (@(s1 or b) !$isunknown({s1,b}) |-> ##0 (c1 == ~(s1 & b)));

  // Output tie-offs to internal nets
  assert property (@(sum or s2)  sum === s2);
  assert property (@(cout or c1) cout === c1);

  // No X/Z on internal/outputs when inputs are known
  assert property (@(a or b) !$isunknown({a,b}) |-> ##0 !$isunknown({s1,s2,c1,sum,cout}));

  // Input space coverage
  cover property (@(a or b) !$isunknown({a,b}) && a==0 && b==0);
  cover property (@(a or b) !$isunknown({a,b}) && a==0 && b==1);
  cover property (@(a or b) !$isunknown({a,b}) && a==1 && b==0);
  cover property (@(a or b) !$isunknown({a,b}) && a==1 && b==1);

  // Functional correctness observed
  cover property (@(a or b) !$isunknown({a,b}) && sum == (a ^ b) && cout == (a & b));

endmodule

bind half_adder_nand half_adder_nand_sva sva_i (
  .a(a), .b(b), .sum(sum), .cout(cout),
  .s1(s1), .s2(s2), .c1(c1)
);