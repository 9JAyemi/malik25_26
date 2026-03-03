// SVA for adder_4bit
// Bind this file to the DUT; focuses on correctness, X-checks, and glitchlessness.

module adder_4bit_sva (
  input logic [3:0] A, B,
  input logic       Cin, Clk,
  input logic [3:0] S,
  input logic       Cout
);
  default clocking cb @(posedge Clk); endclocking

  logic past_v;
  initial past_v = 1'b0;
  always_ff @(posedge Clk) past_v <= 1'b1;

  // Expected 5-bit sum of prior-cycle inputs (registered adder behavior)
  let exp_sum_past = {1'b0,$past(A)} + {1'b0,$past(B)} + $past(Cin);

  // Functional correctness (1-cycle latency)
  a_func:   assert property (past_v |-> {Cout,S} == exp_sum_past);

  // Outputs must never be X/Z once past valid
  a_no_x:   assert property (past_v |-> !$isunknown({S,Cout}));

  // No mid-cycle glitches (sample at negedge for simplicity)
  a_glitch: assert property (@(negedge Clk) $stable({S,Cout}));

  // Coverage: key corners and carry behaviors
  c_cout0:           cover property (past_v && Cout==0);
  c_cout1:           cover property (past_v && Cout==1);
  c_zero:            cover property (past_v && A==4'h0 && B==4'h0 && Cin==0 && S==4'h0 && Cout==0);
  c_full:            cover property (past_v && A==4'hF && B==4'hF && Cin==1 && S==4'hF && Cout==1);
  c_cin_only_carry:  cover property (past_v && A==4'hF && B==4'h0 && Cin==1 && S==4'h0 && Cout==1);
  c_no_carry_with_cin: cover property (past_v && A==4'h0 && B==4'h0 && Cin==1 && S==4'h1 && Cout==0);
  c_boundary:        cover property (past_v && A==4'h8 && B==4'h8 && Cin==0 && S==4'h0 && Cout==1);
endmodule

bind adder_4bit adder_4bit_sva sva_adder_4bit (.*);