// SVA for ripple_carry_adder
module rca_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       carry_in,
  input  logic [3:0] S,
  input  logic       carry_out
);
  // Golden model (5-bit)
  let sum_ext = {1'b0, A} + {1'b0, B} + carry_in;

  // Functional correctness (concise, full check)
  assert property (@(*) {carry_out, S} == sum_ext);

  // No X/Z on outputs when inputs are known
  assert property (@(*) (!$isunknown({A,B,carry_in})) |-> (!$isunknown({S,carry_out})));

  // Coverage: carry/no-carry, extremes, wraparound
  cover property (@(*) sum_ext[4] == 1'b0);
  cover property (@(*) sum_ext[4] == 1'b1);
  cover property (@(*) sum_ext == 5'd0);    // A=B=0, cin=0
  cover property (@(*) sum_ext == 5'd16);   // wrap: S==0, cout==1
  cover property (@(*) (S == 4'hF && !carry_out));
  cover property (@(*) (S == 4'h0 &&  carry_out));
  cover property (@(*) (A==4'h0 && B==4'h0 && carry_in==1'b0));
  cover property (@(*) (A==4'hF && B==4'hF && carry_in==1'b1));
endmodule

bind ripple_carry_adder rca_sva u_rca_sva(.A(A), .B(B), .carry_in(carry_in), .S(S), .carry_out(carry_out));