// SVA for priority_encoder
// Bind into DUT to access internals (stage1_out, stage2_out)
module priority_encoder_sva;

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Combinational stage correctness
  assert property (cb stage1_out == {in[0] & in[1], in[0] | in[1]});

  // Pipeline register behavior
  assert property (cb past_valid |-> stage2_out == $past(stage1_out));

  // Output encoding from stage2_out
  assert property (cb out == {stage2_out[1], stage2_out[0] & ~stage2_out[1]});
  assert property (cb out != 2'b11);

  // Invariant: AND implies OR on registered stage
  assert property (cb disable iff (!past_valid) stage2_out[1] |-> stage2_out[0]);

  // End-to-end (1-cycle latency) mapping from input to output
  assert property (cb past_valid && !$isunknown($past(in)) |->
                      out == { $past(in[0] & in[1]),
                               ($past(in[0] | in[1]) & ~ $past(in[0] & in[1])) });

  // Coverage: all input classes and expected outputs (1-cycle later)
  cover property (cb past_valid && $past(in) == 2'b00 && out == 2'b00);
  cover property (cb past_valid && ($past(in) inside {2'b01,2'b10}) && out == 2'b01);
  cover property (cb past_valid && $past(in) == 2'b11 && out == 2'b10);

endmodule

bind priority_encoder priority_encoder_sva pe_sva();