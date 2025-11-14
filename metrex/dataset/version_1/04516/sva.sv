// SVA for bitwise_or: concise, full functional/timing checks + focused coverage
module bitwise_or_sva (
  input logic        clk,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic [3:0]  stage1_out,
  input logic [3:0]  stage2_out,
  input logic [3:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Start checking only after we have a valid 1-cycle $past history
  logic past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1;
  default disable iff (!past_valid);

  // Sanity: no X/Z on key signals once checking is enabled
  assert property (!$isunknown({a,b,stage1_out,stage2_out,out}));

  // Combinational mirror
  assert property (out == stage2_out);

  // Stage checks
  assert property (stage1_out == $past(a | b));       // OR computed into stage1 (NBA semantics)
  assert property (stage2_out == $past(stage1_out));  // stage2 pipelines stage1

  // End-to-end functional check: 1-cycle latency OR
  assert property (out == $past(a | b));

  // Coverage: change at inputs propagates to output next cycle with correct value
  cover property ($changed(a | b) ##1 (out == $past(a | b) && $changed(out)));

  // Per-bit truth-table coverage observed at inputs and reflected at output next cycle
  genvar i;
  generate for (i=0; i<4; i++) begin : g_or_tt_cov
    cover property (a[i]==0 && b[i]==0 ##1 out[i]==0);
    cover property (a[i]==0 && b[i]==1 ##1 out[i]==1);
    cover property (a[i]==1 && b[i]==0 ##1 out[i]==1);
    cover property (a[i]==1 && b[i]==1 ##1 out[i]==1);
  end endgenerate
endmodule

// Bind to the DUT (accesses internal regs via bind scope)
bind bitwise_or bitwise_or_sva sva_inst (.*);