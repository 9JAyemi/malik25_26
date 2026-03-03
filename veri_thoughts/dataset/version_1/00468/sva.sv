// SVA checker for clock_gate_en
module clock_gate_en_sva (
  input logic clk,
  input logic en,
  input logic data_in,
  input logic data_out
);

  // qualify $past
  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // No-X on critical signals (at sampling edge)
  assert property (!$isunknown(en));
  assert property (!$isunknown(data_in));
  assert property (!$isunknown(data_out));

  // Functional: one-cycle registered behavior
  assert property (data_out == ($past(en) ? $past(data_in) : 1'b0));

  // Coverage of key behaviors
  cover property ($past(en) &&  $past(data_in) &&  data_out); // pass 1
  cover property ($past(en) && !$past(data_in) && !data_out); // pass 0
  cover property (!$past(en) && !data_out);                  // gated to 0
  cover property (!$past(en) && en);                         // 0->1 enable
  cover property ( $past(en) && !en);                        // 1->0 disable

endmodule

// Bind into DUT
bind clock_gate_en clock_gate_en_sva u_clock_gate_en_sva (.*);