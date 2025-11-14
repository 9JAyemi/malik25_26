// SVA for adder4: functional correctness, X-checks, stability, and key corner coverage.
// Uses a combinational event to sample on any input/output change.

module adder4_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] S,
  input logic       COUT
);
  event comb_ev;
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  logic [4:0] exp_sum;
  always_comb exp_sum = {1'b0,A} + {1'b0,B};

  // Functional correctness
  assert property ({COUT, S} == exp_sum);

  // Outputs must not be X/Z when inputs are known
  assert property ( !$isunknown({A,B}) |-> !$isunknown({S,COUT}) );

  // Combinational stability: if inputs don’t change, outputs don’t change
  assert property ( $stable({A,B}) |=> $stable({S,COUT}) );

  // Coverage: no-carry and carry cases, extreme sums, and a wrap-to-zero with carry
  cover property (exp_sum[4] == 1'b0);
  cover property (exp_sum[4] == 1'b1);
  cover property (exp_sum == 5'd0);    // A=0, B=0
  cover property (exp_sum == 5'd15);   // max no-carry sum
  cover property (exp_sum == 5'd16);   // wrap: S==0, COUT==1
  cover property (A==4'hF && B==4'hF); // extreme inputs
  cover property (A==4'h8 && B==4'h8); // mid carry case
endmodule

bind adder4 adder4_sva u_adder4_sva(.A(A), .B(B), .S(S), .COUT(COUT));