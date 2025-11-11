// SVA for edge_detect: concise, high-quality checks and coverage.
// Bindable to the DUT to access internal sig_reg.

module edge_detect_sva (
  input  logic       clk,
  input  logic       rst,
  input  logic       sig,
  input  logic       rise,
  input  logic       fall,
  input  logic [1:0] sig_reg
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (check during reset explicitly)
  assert property (@cb rst |-> (sig_reg == 2'b00 && rise == 1'b0 && fall == 1'b0));

  // All other checks disabled during reset
  default disable iff (rst);

  // State update correctness
  assert property (@cb sig_reg[0] == $past(sig));
  assert property (@cb sig_reg[1] == $past(sig_reg[0]));

  // Output decode correctness
  assert property (@cb rise == (sig_reg == 2'b01));
  assert property (@cb fall == (sig_reg == 2'b10));
  assert property (@cb !(rise && fall));                       // mutual exclusion
  assert property (@cb (sig_reg[0] == sig_reg[1]) |-> (!rise && !fall)); // no spurious pulses

  // Edge-to-pulse behavior and pulse width (one cycle)
  assert property (@cb $rose(sig_reg[0]) |-> (rise && !fall));
  assert property (@cb $fell(sig_reg[0]) |-> (fall && !rise));
  assert property (@cb rise |=> !rise);
  assert property (@cb fall |=> !fall);

  // Known-value check (no X/Z on observable state/outputs)
  assert property (@cb !$isunknown({sig_reg, rise, fall}));

  // Coverage
  cover property (@cb $rose(sig_reg[0]) and rise);
  cover property (@cb $fell(sig_reg[0]) and fall);
  cover property (@cb $rose(sig_reg[0]) ##1 $fell(sig_reg[0])); // rise then fall
  cover property (@cb $fell(sig_reg[0]) ##1 $rose(sig_reg[0])); // fall then rise
endmodule

// Bind example (place in a verification file)
// bind edge_detect edge_detect_sva u_edge_detect_sva (.* , .sig_reg(sig_reg));