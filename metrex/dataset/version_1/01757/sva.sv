// SVA for mux_2x4 (2-to-4 one-hot decoder)
// Focused, high-quality checks and coverage. Bind into DUT.

module mux_2x4_sva (
  input logic [1:0] in,
  input logic [3:0] out
);

  // Sample on any activity of inputs/outputs (combinational DUT)
  default clocking cb @(in or out); endclocking

  // Functional equivalence when input is known (2-state)
  property p_decode_func;
    !$isunknown(in) |-> (out == (4'b0001 << in));
  endproperty
  assert property (p_decode_func);

  // One-hot guarantee when input is known
  property p_onehot_when_known;
    !$isunknown(in) |-> $onehot(out);
  endproperty
  assert property (p_onehot_when_known);

  // Defined behavior for unknown input: all-zero output
  property p_zero_when_unknown;
    $isunknown(in) |-> (out == 4'b0000);
  endproperty
  assert property (p_zero_when_unknown);

  // No spurious glitches: out changes only when in changes
  property p_no_spurious_out_changes;
    !$changed(in) |-> $stable(out);
  endproperty
  assert property (p_no_spurious_out_changes);

  // Functional coverage
  cover property (in == 2'b00 && out == 4'b0001);
  cover property (in == 2'b01 && out == 4'b0010);
  cover property (in == 2'b10 && out == 4'b0100);
  cover property (in == 2'b11 && out == 4'b1000);
  cover property ($isunknown(in) && out == 4'b0000);

endmodule

// Bind into the DUT
bind mux_2x4 mux_2x4_sva u_mux_2x4_sva (.*);