// SVA for pipeline_split and top_module
// Bind these modules after/beside your DUT code

// Assertions for the combinational splitter
module pipeline_split_sva (
  input logic [15:0] in,
  input logic [7:0]  out_hi,
  input logic [7:0]  out_lo
);
  // Functional equivalence
  always @* begin
    assert (out_hi == in[15:8])
      else $error("pipeline_split: out_hi != in[15:8]");
    assert (out_lo == in[7:0])
      else $error("pipeline_split: out_lo != in[7:0]");

    // No X/Z on outputs when input is known
    if (!$isunknown(in)) begin
      assert (!$isunknown({out_hi,out_lo}))
        else $error("pipeline_split: X/Z on outputs with known input");
    end
  end
endmodule

bind pipeline_split pipeline_split_sva ps_sva (
  .in(in),
  .out_hi(out_hi),
  .out_lo(out_lo)
);

// Assertions for the pipelined top level
module top_module_sva (
  input  logic        clk,
  input  logic [15:0] in,
  input  logic [7:0]  stage1_out_hi,
  input  logic [7:0]  stage1_out_lo,
  input  logic [7:0]  out_hi,
  input  logic [7:0]  out_lo
);
  default clocking cb @(posedge clk); endclocking

  // Guard for $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Stage1 comb result must match current input split
  assert property (stage1_out_hi == in[15:8] && stage1_out_lo == in[7:0])
    else $error("top_module: stage1 != in split");

  // Registered outputs must equal previous cycle's stage1
  assert property (past_valid |-> (out_hi == $past(stage1_out_hi) &&
                                   out_lo == $past(stage1_out_lo)))
    else $error("top_module: outputs != $past(stage1)");

  // End-to-end: outputs equal previous cycle input (1-cycle latency)
  assert property (past_valid |-> ({out_hi,out_lo} == $past(in)))
    else $error("top_module: outputs != $past(in)");

  // No X/Z on outputs when previous input was known
  assert property (past_valid && !$isunknown($past(in)) |-> !$isunknown({out_hi,out_lo}))
    else $error("top_module: X/Z on outputs with known $past(in)");

  // Light functional coverage
  cover property (past_valid && {out_hi,out_lo} == $past(in));
  cover property (past_valid && out_hi != out_lo); // show independence of halves
  cover property (past_valid && out_hi != $past(out_hi) && out_lo == $past(out_lo)); // hi changes only
  cover property (past_valid && out_lo != $past(out_lo) && out_hi == $past(out_hi)); // lo changes only
  cover property (past_valid && $past(in) == 16'h0000 && {out_hi,out_lo} == 16'h0000);
  cover property (past_valid && $past(in) == 16'hFFFF && {out_hi,out_lo} == 16'hFFFF);
  cover property (past_valid && $past(in) == 16'hAA55 && {out_hi,out_lo} == 16'hAA55);
endmodule

bind top_module top_module_sva tm_sva (
  .clk(clk),
  .in(in),
  .stage1_out_hi(stage1_out_hi),
  .stage1_out_lo(stage1_out_lo),
  .out_hi(out_hi),
  .out_lo(out_lo)
);