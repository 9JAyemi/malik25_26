// SVA for binary_adder and full_adder
// Bind these checkers in your TB and drive a free-running clk.

module full_adder_sva (
  input logic clk,
  input logic A, B, C_in,
  input logic S, C_out
);
  default clocking cb @ (posedge clk); endclocking

  // Sanity
  a_fa_no_x_in:  assert property (!$isunknown({A,B,C_in}));
  a_fa_no_x_out: assert property (!$isunknown({S,C_out}));

  // Functionality
  a_fa_sum:  assert property ({C_out,S} == (A + B + C_in));
  a_fa_s:    assert property (S == (A ^ B ^ C_in));
  a_fa_cout: assert property (C_out == ((A & B) | (A & C_in) | (B & C_in)));

  // Coverage: exercise all 8 input combinations
  c_fa_000: cover property ({A,B,C_in} == 3'b000);
  c_fa_001: cover property ({A,B,C_in} == 3'b001);
  c_fa_010: cover property ({A,B,C_in} == 3'b010);
  c_fa_011: cover property ({A,B,C_in} == 3'b011);
  c_fa_100: cover property ({A,B,C_in} == 3'b100);
  c_fa_101: cover property ({A,B,C_in} == 3'b101);
  c_fa_110: cover property ({A,B,C_in} == 3'b110);
  c_fa_111: cover property ({A,B,C_in} == 3'b111);
endmodule


module binary_adder_sva (
  input logic clk,
  input logic [3:0] A, B,
  input logic [3:0] S,
  input logic C
);
  default clocking cb @ (posedge clk); endclocking

  // Sanity
  a_ba_no_x_in:  assert property (!$isunknown({A,B}));
  a_ba_no_x_out: assert property (!$isunknown({S,C}));

  // Overall correctness
  a_ba_sum: assert property ({C,S} == (A + B));

  // Bit-accurate ripple checks (derived only from A,B)
  let c1 = (A[0] & B[0]);
  let c2 = (A[1] & B[1]) | (A[1] & c1) | (B[1] & c1);
  let c3 = (A[2] & B[2]) | (A[2] & c2) | (B[2] & c2);
  let c4 = (A[3] & B[3]) | (A[3] & c3) | (B[3] & c3);

  a_s0: assert property (S[0] == (A[0] ^ B[0]));
  a_s1: assert property (S[1] == (A[1] ^ B[1] ^ c1));
  a_s2: assert property (S[2] == (A[2] ^ B[2] ^ c2));
  a_s3: assert property (S[3] == (A[3] ^ B[3] ^ c3));
  a_co: assert property (C == c4);

  // Useful coverage
  c_no_carry: cover property (C == 1'b0);
  c_carry:    cover property (C == 1'b1);
  c_zero:     cover property (A == 4'h0 && B == 4'h0);
  c_max_max:  cover property (A == 4'hF && B == 4'hF);
  c_zero_max: cover property (A == 4'h0 && B == 4'hF);
  c_max_zero: cover property (A == 4'hF && B == 4'h0);
  c_onehots:  cover property ($onehot(A) && $onehot(B));
  c_boundary: cover property ((A + B) == 4'hF); // max sum without carry
endmodule


// Example binds (connect .clk to a TB clock)
bind full_adder   full_adder_sva   u_full_adder_sva   (.clk(clk), .A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out));
bind binary_adder binary_adder_sva u_binary_adder_sva (.clk(clk), .A(A), .B(B), .S(S), .C(C));