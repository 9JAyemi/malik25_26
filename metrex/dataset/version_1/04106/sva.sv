// SVA for rising_edge_detector
// Bind into the DUT; references DUT internals directly.
module rising_edge_detector_sva;
  // Visible signals come from bound scope (rising_edge_detector)
  // clk, reset, in, out, pipeline_reg

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior
  ap_reset_clears: assert property (reset |=> (pipeline_reg[0]==32'h0 &&
                                               pipeline_reg[1]==32'h0 &&
                                               pipeline_reg[2]==32'h0 &&
                                               out==32'h0));

  // No X/Z after reset
  ap_no_x: assert property (!$isunknown({out, pipeline_reg[0], pipeline_reg[1], pipeline_reg[2]}));

  // Pipeline shift integrity (only when there was a valid prior non-reset cycle)
  ap_shift0: assert property (!$past(reset) |-> (pipeline_reg[0] == $past(in)));
  ap_shift1: assert property (!$past(reset) |-> (pipeline_reg[1] == $past(pipeline_reg[0])));
  ap_shift2: assert property (!$past(reset) |-> (pipeline_reg[2] == $past(pipeline_reg[1])));

  // Output equals function of prior pipeline state (vector-wise)
  ap_out_eq_pipe: assert property (!$past(reset) |-> out == $past(pipeline_reg[0] & ~pipeline_reg[1] & pipeline_reg[2]));

  // Output equals 3-cycle history of input (documents actual behavior)
  ap_out_vs_in: assert property (!$past(reset,3) |-> out == ($past(in,1) & ~$past(in,2) & $past(in,3)));

  // Coverage: observe at least one 1-0-1 detection and out assertion
  cp_detect_101_then_out: cover property (!$past(reset) and
                                          ($past(pipeline_reg[0] & ~pipeline_reg[1] & pipeline_reg[2]) != 32'h0)
                                          ##1 (out != 32'h0));

  // Coverage: observe simple rising edge on any bit of input
  cp_any_rise_on_in:    cover property ((in & ~$past(in)) != 32'h0);

  // Optional spec check (commented): typical rising-edge detector would be out == $past(in) & ~$past(in,2)
  // Uncomment if that is the intended spec (will fail with current RTL):
  // ap_spec_rise: assert property (!$past(reset,2) |-> out == ($past(in,1) & ~$past(in,2)));
endmodule

bind rising_edge_detector rising_edge_detector_sva sva_inst();