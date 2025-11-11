// SVA for pipeline_splitter
module pipeline_splitter_sva (
  input  logic        clk,
  input  logic [15:0] in,
  input  logic [7:0]  out_hi,
  input  logic [7:0]  out_lo,
  input  logic [15:0] stage1_out,
  input  logic [7:0]  stage2_out
);
  default clocking cb @(posedge clk); endclocking

  // enable checks after pipeline fill (1 and 2 cycles)
  bit v1, v2;
  initial begin v1 = 0; v2 = 0; end
  always_ff @(posedge clk) begin
    v1 <= 1'b1;
    v2 <= v1;
  end

  // Structural wiring
  assert property (out_lo == stage1_out[15:8]);
  assert property (out_hi == stage2_out);

  // Per-stage latency and function
  assert property (v1 |-> stage1_out == $past(in));
  assert property (v1 |-> stage2_out == $past(stage1_out[7:0]));

  // End-to-end behavior
  assert property (v1 |-> out_lo == $past(in[15:8]));
  assert property (v2 |-> out_hi == $past(in[7:0], 2));

  // Change propagation guarantees
  assert property (v1 && $changed(in[15:8]) |-> ##1 $changed(out_lo));
  assert property (v2 && $changed(in[7:0])  |-> ##2 $changed(out_hi));

  // Coverage: observe both legs, and independence scenarios
  cover property (v1 && v2 && out_lo == $past(in[15:8]) && out_hi == $past(in[7:0],2));
  cover property (v2 && $stable(in[15:8]) && $changed(in[7:0])  ##2 $changed(out_hi) && $stable(out_lo));
  cover property (v2 && $stable(in[7:0])  && $changed(in[15:8]) ##1 $changed(out_lo) ##1 $stable(out_hi));
endmodule

bind pipeline_splitter pipeline_splitter_sva sva (.*);