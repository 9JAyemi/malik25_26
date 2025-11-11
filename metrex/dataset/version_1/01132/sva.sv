// SVA for pipeline_registers
// Focus: correctness of 3-stage latency, width handling (truncate/extend), X-propagation, and basic coverage.

module pipeline_registers_sva #(
  parameter int n = 4,
  parameter int m = 2,
  parameter int s = 3
)(
  input  logic              clk,
  input  logic [n-1:0]      in,
  input  logic [m-1:0]      out,
  input  logic [n-1:0]      stage1_reg,
  input  logic [n-1:0]      stage2_reg,
  input  logic [n-1:0]      stage3_reg
);
  default clocking cb @ (posedge clk); endclocking

  // Track minimum history for $past(...,3)
  int unsigned cycles;
  initial cycles = 0;
  always_ff @(posedge clk) if (cycles < 3) cycles <= cycles + 1;
  wire v1 = (cycles >= 1);
  wire v2 = (cycles >= 2);
  wire v3 = (cycles >= 3);

  // Parameter consistency: design hardcodes 3 pipeline regs
  initial assert (s == 3)
    else $error("pipeline_registers: parameter s (%0d) must equal 3 to match 3 pipeline registers", s);

  // Stage correctness w.r.t. input history
  assert property (disable iff (!v1) stage1_reg == $past(in));
  assert property (disable iff (!v2) stage2_reg == $past(in,2));
  assert property (disable iff (!v3) stage3_reg == $past(in,3));

  // Output mapping and width semantics
  if (m <= n) begin
    assert property (disable iff (!v3) out == stage3_reg[m-1:0]);
    assert property (disable iff (!v3) out == $past(in,3)[m-1:0]);
  end else begin
    assert property (disable iff (!v3) out[n-1:0] == stage3_reg);
    assert property (disable iff (!v3) out[m-1:n] == '0);
    assert property (disable iff (!v3) out == {{(m-n){1'b0}}, $past(in,3)});
  end

  // X-propagation: known inputs over the necessary history imply known output
  function automatic bit known_vec(input logic [n-1:0] v); return !$isunknown(v); endfunction
  assert property (disable iff (!v3)
                   known_vec($past(in)) && known_vec($past(in,2)) && known_vec($past(in,3))
                   |-> !$isunknown(out));

  // Minimal functional coverage: observe a change propagating through the pipeline
  cover property (v3 && $changed(in) ##1 $changed(stage1_reg) ##1 $changed(stage2_reg) ##1 $changed(out));
endmodule

bind pipeline_registers pipeline_registers_sva #(.n(n), .m(m), .s(s))
  i_pipeline_registers_sva (
    .clk(clk),
    .in(in),
    .out(out),
    .stage1_reg(stage1_reg),
    .stage2_reg(stage2_reg),
    .stage3_reg(stage3_reg)
  );