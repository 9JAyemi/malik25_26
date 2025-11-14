// SVA for full_adder and 4-bit ripple_carry_adder
// Concise, high-quality functional checking with essential coverage.

module fa_sva (
  input logic a, b, cin,
  input logic sum, cout
);
  default clocking cb @(*); endclocking

  // Outputs must be known when inputs are known
  assert property (!$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout}));

  // Functional correctness: 2-bit result equals a+b+cin
  assert property (disable iff ($isunknown({a,b,cin,sum,cout}))
                   {cout,sum} == ({1'b0,a}+{1'b0,b}+{1'b0,cin}));

  // Minimal full input-space coverage (8 combinations)
  cover property (! $isunknown({a,b,cin}) && {a,b,cin}==3'b000);
  cover property (! $isunknown({a,b,cin}) && {a,b,cin}==3'b001);
  cover property (! $isunknown({a,b,cin}) && {a,b,cin}==3'b010);
  cover property (! $isunknown({a,b,cin}) && {a,b,cin}==3'b011);
  cover property (! $isunknown({a,b,cin}) && {a,b,cin}==3'b100);
  cover property (! $isunknown({a,b,cin}) && {a,b,cin}==3'b101);
  cover property (! $isunknown({a,b,cin}) && {a,b,cin}==3'b110);
  cover property (! $isunknown({a,b,cin}) && {a,b,cin}==3'b111);
endmodule

bind full_adder fa_sva(.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));



module rca4_sva (
  input  logic [3:0] A, B,
  input  logic [4:0] sum,
  input  logic [3:0] carry   // internal net from DUT
);
  default clocking cb @(*); endclocking

  // Outputs must be known when inputs are known
  assert property (!$isunknown({A,B}) |-> ##0 !$isunknown(sum));

  // Functional correctness: 5-bit sum equals zero-extended A+B
  assert property (disable iff ($isunknown({A,B,sum}))
                   sum == ({1'b0,A} + {1'b0,B}));

  // Carry chain correctness (generate/propagate form)
  assert property (disable iff ($isunknown({A[0],B[0],carry[0]}))
                   carry[0] == (A[0] & B[0]));
  assert property (disable iff ($isunknown({A[1],B[1],carry[0],carry[1]}))
                   carry[1] == (A[1] & B[1]) | ((A[1]^B[1]) & carry[0]));
  assert property (disable iff ($isunknown({A[2],B[2],carry[1],carry[2]}))
                   carry[2] == (A[2] & B[2]) | ((A[2]^B[2]) & carry[1]));
  assert property (disable iff ($isunknown({A[3],B[3],carry[2],sum[4]}))
                   sum[4]   == (A[3] & B[3]) | ((A[3]^B[3]) & carry[2]));

  // Bit-level sum checks per stage
  assert property (disable iff ($isunknown({A[0],B[0],sum[0]}))
                   sum[0] == (A[0]^B[0]));
  assert property (disable iff ($isunknown({A[1],B[1],carry[0],sum[1]}))
                   sum[1] == (A[1]^B[1]^carry[0]));
  assert property (disable iff ($isunknown({A[2],B[2],carry[1],sum[2]}))
                   sum[2] == (A[2]^B[2]^carry[1]));
  assert property (disable iff ($isunknown({A[3],B[3],carry[2],sum[3]}))
                   sum[3] == (A[3]^B[3]^carry[2]));

  // Focused coverage: extremes, carry-out, and long ripple
  cover property (! $isunknown({A,B,sum}) && (A==4'h0) && (B==4'h0) && (sum==5'd0));
  cover property (! $isunknown({A,B,sum}) && (A==4'hF) && (B==4'hF) && (sum==5'd30));
  cover property (! $isunknown({A,B,sum}) && sum[4] == 1'b1);
  cover property (! $isunknown({A,B}) && (A==4'hF) && (B==4'h1)); // 4-stage propagate
  cover property (! $isunknown({A,B}) && (A==4'h1) && (B==4'hF)); // symmetric
  cover property (! $isunknown(carry) && carry[0]);
  cover property (! $isunknown(carry) && carry[1]);
  cover property (! $isunknown(carry) && carry[2]);
endmodule

bind ripple_carry_adder rca4_sva(.A(A), .B(B), .sum(sum), .carry(carry));