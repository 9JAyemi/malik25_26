// SVA checker for ones_complement
module ones_complement_sva (
    input logic        clk,
    input logic [3:0]  binary,
    input logic [3:0]  ones_comp,
    input logic [3:0]  stage1_out,
    input logic [3:0]  stage2_out
);

  default clocking cb @(posedge clk); endclocking

  // Guard for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Combinational stage checks (sampled on clk)
  assert property (stage1_out == ~binary)
    else $error("Stage1 mismatch: stage1_out != ~binary");

  assert property (stage2_out == ~stage1_out)
    else $error("Stage2 mismatch: stage2_out != ~stage1_out");

  // Registered output follows stage2_out (1-cycle latency)
  assert property (disable iff (!past_valid) ones_comp == $past(stage2_out))
    else $error("Output reg mismatch: ones_comp != $past(stage2_out)");

  // End-to-end pipeline behavior (redundant with above + stage2, but concise)
  assert property (disable iff (!past_valid) ones_comp == $past(binary))
    else $error("Pipeline mismatch: ones_comp != $past(binary)");

  // X/Z hygiene: known in -> known through -> known out next cycle
  assert property (!$isunknown(binary) |-> (!$isunknown(stage1_out) && !$isunknown(stage2_out)))
    else $error("Unknowns propagated in combinational stages");

  assert property (disable iff (!past_valid) !$isunknown($past(binary)) |-> !$isunknown(ones_comp))
    else $error("Unknown on ones_comp when prior binary was known");

  // Functional coverage
  // - Each value seen on binary is observed on ones_comp one cycle later
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : CVAL
      cover property (disable iff (!past_valid)
                      (binary == i[3:0]) ##1 (ones_comp == i[3:0]));
    end
  endgenerate

  // - A change on binary causes a change on ones_comp one cycle later
  cover property (disable iff (!past_valid) $changed(binary) ##1 $changed(ones_comp));

endmodule

// Bind into the DUT
bind ones_complement ones_complement_sva sva_inst (.*);