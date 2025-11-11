// SVA for add/sub with signed overflow checks, plus concise coverage.
// Bind this to the DUT and drive clk/rst_n from your environment.
//
// Example bind (in your testbench):
//   bind addsub_32 addsub_32_sva sva_i(.clk(clk), .rst_n(rst_n), .A(A), .B(B), .C(C), .S(S), .V(V));

module addsub_32_sva (
  input logic clk, rst_n,
  input  signed [31:0] A, B,
  input  logic         C,
  input  signed [31:0] S,
  input  logic         V
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity
  a_known_inputs:  assert property (!$isunknown({A,B,C}));
  a_known_outputs: assert property (!$isunknown({S,V}));

  // Functional intent: C==0 => add; C==1 => subtract
  a_add: assert property ((!C) |-> (S == (A + B)));
  a_sub: assert property (( C) |-> (S == (A - B)));

  // Signed overflow flags (two’s complement)
  // Add overflow: same-sign inputs, sign flips in result
  a_V_add: assert property ((!C) |-> (V == ((~(A[31]^B[31])) &  (A[31]^S[31]))));
  // Sub overflow: different-sign inputs, sign flips vs A
  a_V_sub: assert property (( C) |-> (V == ( (A[31]^B[31])  &  (A[31]^S[31]))));

  // Identities
  a_add_id0: assert property ((!C && (B==0)) |-> (S==A));
  a_sub_id0: assert property (( C && (B==0)) |-> (S==A));
  a_sub_zero_when_equal: assert property ((C && (A==B)) |-> (S==0));

  // Combinational stability: if inputs stable, outputs stable
  a_stable: assert property ($stable({A,B,C}) |-> $stable({S,V}));

  // Minimal, targeted coverage
  c_mode_add: cover property (!C);
  c_mode_sub: cover property ( C);

  c_add_zero: cover property (!C && (S==0));
  c_sub_zero: cover property ( C && (S==0));

  c_add_overflow: cover property (!C && ((~(A[31]^B[31])) & (A[31]^S[31]) & V));
  c_sub_overflow: cover property ( C && ( (A[31]^B[31])  & (A[31]^S[31]) & V));

  // Corner cases hitting overflow edges
  c_add_max_plus_1: cover property (!C && (A==32'sh7fff_ffff) && (B==32'sh0000_0001) && V);
  c_sub_min_minus_1: cover property ( C && (A==32'sh8000_0000) && (B==32'sh0000_0001) && V);

endmodule


// Optional: lightweight implementation-consistency checks against internal structure.
// Bind if you want to ensure the RTL wiring matches its own expressions.
// Example:
//   bind addsub_32 addsub_32_impl_sva impl_i(.clk(clk), .rst_n(rst_n));
module addsub_32_impl_sva (input logic clk, rst_n);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Access DUT internals directly in bound scope
  // sum == A + ~B + C
  a_sum_impl: assert property ({1'b0, sum} == $signed({1'b0, A}) + $signed({1'b0, ~B}) + C);

  // Output mux: S == sum when C, else two’s complement of sum
  a_mux_impl: assert property (C ? (S==sum) : (S==(~sum + 1)));

  // Overflow as coded
  a_V_impl: assert property (V == ((A[31]==B[31]) && (A[31]!=sum[31])));

  // Known-ness of key internal nets
  a_known_int: assert property (!$isunknown({sum, V}));

endmodule