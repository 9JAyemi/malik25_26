// SVA for pipelined_circuit (binds into the DUT; no DUT edits needed)
module pipelined_circuit_sva(
  input logic [3:0] in,
  input logic       out_and,
  input logic       out_or,
  input logic       out_xor,
  input logic [3:0] stage1_out,
  input logic [2:0] stage2_out
);
  default clocking cb @(*) ; endclocking
  default disable iff ($isunknown(in))

  // Stage 1 correctness
  a_s1_0: assert property (##0 stage1_out[0] == (in[0] & in[1]));
  a_s1_1: assert property (##0 stage1_out[1] == (in[2] & in[3]));
  a_s1_2: assert property (##0 stage1_out[2] == (stage1_out[0] | stage1_out[1]));
  a_s1_3: assert property (##0 stage1_out[3] == (stage1_out[0] ^ stage1_out[1]));

  // Stage 2 correctness
  a_s2_0: assert property (##0 stage2_out[0] == (stage1_out[0] & stage1_out[1]));
  a_s2_1: assert property (##0 stage2_out[1] == (stage1_out[2] | stage1_out[3]));
  a_s2_2: assert property (##0 stage2_out[2] == (stage1_out[2] ^ stage1_out[3]));
  // Algebraic invariant of this design: (a|b)^(a^b) == a&b
  a_s2_rel: assert property (##0 stage2_out[2] == stage2_out[0]);

  // Output wiring
  a_o_and: assert property (##0 out_and == stage2_out[0]);
  a_o_or : assert property (##0 out_or  == stage2_out[1]);
  a_o_xor: assert property (##0 out_xor == stage2_out[2]);

  // End-to-end functional checks (inputs-only reference)
  a_e2e_and: assert property (##0 out_and == (&in));
  a_e2e_or : assert property (##0 out_or  == ((in[0]&in[1]) | (in[2]&in[3])));
  a_e2e_xor: assert property (##0 out_xor == (&in)); // equals out_and

  // No-X on internal/outputs when inputs are known
  a_clean: assert property (##0 !$isunknown({stage1_out,stage2_out,out_and,out_or,out_xor}));

  // Coverage: exercise all (stage1_out[0], stage1_out[1]) cases and output activity
  c_s1_00: cover property (##0 {stage1_out[0],stage1_out[1]}==2'b00);
  c_s1_01: cover property (##0 {stage1_out[0],stage1_out[1]}==2'b01);
  c_s1_10: cover property (##0 {stage1_out[0],stage1_out[1]}==2'b10);
  c_s1_11: cover property (##0 {stage1_out[0],stage1_out[1]}==2'b11);

  c_and_r:  cover property ($rose(out_and));
  c_and_f:  cover property ($fell(out_and));
  c_or_r :  cover property ($rose(out_or));
  c_or_f :  cover property ($fell(out_or));
  c_xor_r:  cover property ($rose(out_xor));
  c_xor_f:  cover property ($fell(out_xor));

  c_or_only: cover property (##0 out_or && !out_and); // cases 01,10
  c_all1  :  cover property (##0 (&in));              // 1111
endmodule

bind pipelined_circuit pipelined_circuit_sva pc_sva_i(
  .in(in),
  .out_and(out_and),
  .out_or(out_or),
  .out_xor(out_xor),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out)
);