// SVA for reg_module: concise, high-quality checks and coverage
// Bind into DUT without modifying it
bind reg_module reg_module_sva sva_inst (.*);

module reg_module_sva (
  input clk,
  input reset,
  input wenb,
  input [7:0] in_data,
  input [7:0] reg_out
);

  // Clocking and past-valid guard
  default clocking cb @(posedge clk); endclocking
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // X-checks (flag any X/Z on critical signals)
  a_xcheck_inputs:  assert property (!$isunknown({reset, wenb, in_data})));
  a_xcheck_output:  assert property (!$isunknown(reg_out));

  // Reset behavior: if reset was asserted last cycle, output must be 0 now
  a_reset_sets_zero: assert property ($past(reset) |-> reg_out == 8'h00);

  // Write behavior: if last cycle had wenb and no reset, capture in_data
  a_write_updates:   assert property ($past(!reset && wenb) |-> reg_out == $past(in_data));

  // Hold behavior: if last cycle had no reset and no write, hold value
  a_hold_when_idle:  assert property ($past(!reset && !wenb) |-> reg_out == $past(reg_out));

  // Change cause: any change must be due to reset or a qualified write
  a_change_has_cause: assert property
    ( (reg_out != $past(reg_out)) |-> ($past(reset) || $past(!reset && wenb)) );

  // Priority check (explicit): reset dominates write when both high
  a_reset_priority:  assert property ($past(reset && wenb) |-> reg_out == 8'h00);

  // Coverage: exercise reset, write, and hold scenarios
  c_reset_pulse:     cover property (reset ##1 !reset);
  c_write_event:     cover property ($past(!reset && wenb) && (reg_out == $past(in_data)));
  c_hold_event:      cover property ($past(!reset && !wenb) && (reg_out == $past(reg_out)));
  c_b2b_writes:      cover property ($past(!reset && wenb) && (!reset && wenb));
  c_reset_then_write:cover property ($past(reset) && (!reset && wenb));

endmodule