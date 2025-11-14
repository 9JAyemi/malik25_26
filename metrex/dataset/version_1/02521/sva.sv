// SVA for pipelined_xor_gate and its pipeline stages
// Bind-ready, concise, and focused on latency/function correctness.

`timescale 1ns/1ps

// Checker for pipelined_xor_gate
module sva_pipelined_xor_gate
(
  input logic clk,
  input logic a, b,
  input logic out_assign,
  input logic a_reg, b_reg,
  input logic xor_out,
  input logic out_assign_reg
);
  // past-valid tracking
  logic pv1, pv2;
  initial begin pv1 = 0; pv2 = 0; end
  always @(posedge clk) begin
    pv1 <= 1'b1;
    pv2 <= pv1;
  end

  default clocking cb @(posedge clk); endclocking

  // Stage-1 capture
  assert property (disable iff (!pv1) a_reg == $past(a));
  assert property (disable iff (!pv1) b_reg == $past(b));

  // XOR combinational correctness (sampled on clk)
  assert property (xor_out == (a_reg ^ b_reg));

  // Stage-2 capture
  assert property (disable iff (!pv1) out_assign_reg == $past(xor_out));

  // Output wiring
  assert property (out_assign == out_assign_reg);

  // End-to-end, 2-cycle latency: out = a^b delayed by 2 clocks
  assert property (disable iff (!pv2) out_assign == $past(a ^ b, 2));

  // Coverage
  cover property (pv2 && out_assign == 1'b0);
  cover property (pv2 && out_assign == 1'b1);
  cover property (pv1 && {a,b} == 2'b00);
  cover property (pv1 && {a,b} == 2'b01);
  cover property (pv1 && {a,b} == 2'b10);
  cover property (pv1 && {a,b} == 2'b11);
  // Observe a/b change and corresponding out change two cycles later
  cover property (pv2 && ($changed(a) || $changed(b)) ##2 $changed(out_assign));
endmodule

// Checker for pipeline_stage_1
module sva_pipeline_stage_1
(
  input logic clk,
  input logic a, b,
  input logic a_reg, b_reg
);
  logic pv1; initial pv1 = 0;
  always @(posedge clk) pv1 <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  assert property (disable iff (!pv1) a_reg == $past(a));
  assert property (disable iff (!pv1) b_reg == $past(b));

  // Coverage: all input combos and register toggles
  cover property (pv1 && {a,b} == 2'b00);
  cover property (pv1 && {a,b} == 2'b01);
  cover property (pv1 && {a,b} == 2'b10);
  cover property (pv1 && {a,b} == 2'b11);
  cover property (pv1 && $changed(a_reg));
  cover property (pv1 && $changed(b_reg));
endmodule

// Checker for pipeline_stage_2
module sva_pipeline_stage_2
(
  input logic clk,
  input logic xor_out,
  input logic out_assign_reg
);
  logic pv1; initial pv1 = 0;
  always @(posedge clk) pv1 <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  assert property (disable iff (!pv1) out_assign_reg == $past(xor_out));

  // Coverage: input/output exercise
  cover property (pv1 && $changed(xor_out));
  cover property (pv1 && $changed(out_assign_reg));
endmodule

// Example binds (instantiate these in your testbench or a bind file):
// bind pipelined_xor_gate    sva_pipelined_xor_gate    u_sva_pipelined_xor_gate (.*);
// bind pipeline_stage_1      sva_pipeline_stage_1      u_sva_pipeline_stage_1   (.*);
// bind pipeline_stage_2      sva_pipeline_stage_2      u_sva_pipeline_stage_2   (.*);