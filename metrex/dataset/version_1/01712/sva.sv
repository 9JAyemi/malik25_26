// SVA checker for and_pipeline
module and_pipeline_sva (
  input logic clk,
  input logic a,
  input logic b,
  input logic stage1_out,
  input logic stage2_out,
  input logic out
);

  // History-valid flags
  logic past1 = 1'b0, past2 = 1'b0, past3 = 1'b0;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
    past3 <= past2;
  end

  default clocking cb @(posedge clk); endclocking

  // Per-stage correctness
  assert property (disable iff (!past1) stage1_out == $past(a & b));
  assert property (disable iff (!past1) stage2_out == $past(stage1_out));
  assert property (disable iff (!past1) out        == $past(stage2_out));

  // End-to-end 3-cycle latency and functional equivalence
  assert property (disable iff (!past3) out == $past(a & b, 3));

  // Known-value checks after pipeline fill
  assert property (disable iff (!past1) !$isunknown(stage1_out));
  assert property (disable iff (!past2) !$isunknown(stage2_out));
  assert property (disable iff (!past3) !$isunknown(out));

  // Glitch-free flops (no mid-cycle updates)
  assert property (@(negedge clk) $stable(stage1_out) && $stable(stage2_out) && $stable(out));

  // Coverage: exercise both values and toggles through the pipeline
  cover property (disable iff (!past3)  (a & b) ##3  out);
  cover property (disable iff (!past3) !(a & b) ##3 !out);
  cover property (disable iff (!past3) ((a & b) != $past(a & b)) ##3 (out != $past(out)));

endmodule

// Bind into the DUT
bind and_pipeline and_pipeline_sva i_and_pipeline_sva (
  .clk(clk),
  .a(a),
  .b(b),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out),
  .out(out)
);