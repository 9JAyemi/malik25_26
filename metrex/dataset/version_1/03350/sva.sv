// SVA for bit_selector
// Checks functional intent, X-safety, and update timing; includes concise coverage.

module bit_selector_sva (
  input logic [3:0] in_signal,
  input logic       control_signal,
  input logic [1:0] out_signal
);

  // Functional correctness: at each posedge, out = ~in[3:2] sampled at previous posedge
  // Guard with $past(1) to skip first edge.
  property p_func_update;
    @(posedge control_signal)
      $past(1'b1) |-> (out_signal == ~$past(in_signal[3:2]));
  endproperty
  assert property (p_func_update);

  // Inputs known at sampling edge; outputs known after first update
  assert property (@(posedge control_signal) !$isunknown(in_signal[3:2]));
  assert property (@(posedge control_signal) $past(1'b1) |-> !$isunknown(out_signal));

  // Output changes only on a rising edge of control_signal (no glitches)
  assert property ( $changed(out_signal) |-> $rose(control_signal) );

  // Coverage: see all mappings from in[3:2] -> out on the following edge
  cover property (@(posedge control_signal) in_signal[3:2]==2'b00 ##1 out_signal==2'b11);
  cover property (@(posedge control_signal) in_signal[3:2]==2'b01 ##1 out_signal==2'b10);
  cover property (@(posedge control_signal) in_signal[3:2]==2'b10 ##1 out_signal==2'b01);
  cover property (@(posedge control_signal) in_signal[3:2]==2'b11 ##1 out_signal==2'b00);

  // Hit at least one update edge
  cover property (@(posedge control_signal) 1'b1);

endmodule

// Bind example (uncomment in your environment):
// bind bit_selector bit_selector_sva sva_inst (.*);