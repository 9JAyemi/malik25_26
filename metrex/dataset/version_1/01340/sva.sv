// SVA for pipeline_register
// Bind this module to the DUT for checks and coverage.

module pipeline_register_sva #(parameter W=32) (
  input  logic              clk,
  input  logic              reset,
  input  logic [W-1:0]      data_in,
  input  logic [W-1:0]      data_out,
  input  logic [W-1:0]      data_reg
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_clk_known:   assert property (@(posedge clk) 1); // ensure a clock exists
  a_reset_known: assert property (@(posedge clk) !$isunknown(reset));

  // Output mirrors internal register at all times
  a_out_eq_reg:  assert property (@(posedge clk) data_out == data_reg);

  // Synchronous reset clears register/output on next cycle
  a_sync_reset_clear: assert property (reset |=> (data_reg == '0 && data_out == '0));

  // 1-cycle pipeline latency when not in reset
  a_latency: assert property (!reset |=> (data_reg == $past(data_in) && data_out == $past(data_in)));

  // While reset held, output stays cleared (redundant but explicit)
  a_hold_zero_while_reset: assert property ($past(reset) && reset |-> (data_reg == '0 && data_out == '0));

  // No X on output after a reset cycle
  a_no_x_after_reset: assert property (reset |=> (!$isunknown(data_reg) && !$isunknown(data_out)));

  // If previous cycle was not reset and input was known, output must be known
  a_known_out_when_prev_in_known: assert property (!$past(reset) && !$isunknown($past(data_in)) |-> !$isunknown(data_out));

  // If two consecutive cycles are active (no reset) and input is stable, output is stable
  a_stable_when_input_stable: assert property (!reset && !$past(reset) && $stable(data_in) |=> $stable(data_out));

  // Coverage
  c_reset_pulse:           cover property (reset ##1 !reset);
  c_reset_held_multi:      cover property (reset [*2]);
  c_pass_through_any:      cover property (!reset ##1 (data_out == $past(data_in)));
  c_back_to_back_updates:  cover property (!reset && (data_in != $past(data_in))
                                           ##1 (data_out == $past(data_in))
                                           ##1 !reset && (data_in != $past(data_in))
                                           ##1 (data_out == $past(data_in)));
  c_zero_to_nonzero:       cover property (reset ##1 !reset && (data_in != '0) ##1 (data_out == $past(data_in)));

endmodule

// Bind into the DUT (connect internal data_reg)
bind pipeline_register pipeline_register_sva #(.W(32)) u_pipeline_register_sva (
  .clk      (clk),
  .reset    (reset),
  .data_in  (data_in),
  .data_out (data_out),
  .data_reg (data_reg)
);