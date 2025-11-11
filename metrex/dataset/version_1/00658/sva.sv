// SVA for shift_register_comparator
// Bind this module to the DUT to check behavior and collect coverage.

module shift_register_comparator_sva
(
  input  logic        clk,
  input  logic        reset,
  input  logic        serial_data,
  input  logic [7:0]  parallel_data,
  input  logic        match,
  input  logic [7:0]  shift_reg
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Track when we are in an active (non-reset) cycle
  logic past_valid;
  always @(posedge clk) past_valid <= !reset;

  // Reset behavior: synchronous clear
  a_reset_clears: assert property (reset |-> (shift_reg == 8'h00 && match == 1'b0))
    else $error("Reset did not clear shift_reg/match");

  // Shift behavior: new shift_reg equals {old[6:0], current serial_data}
  a_shift: assert property (past_valid |-> shift_reg == { $past(shift_reg)[6:0], serial_data })
    else $error("Shift behavior incorrect");

  // Match behavior: match reflects comparison of previous shift_reg to current parallel_data
  a_match_func: assert property (past_valid |-> match == ($past(shift_reg) == parallel_data))
    else $error("Match output incorrect");

  // No X/Z on key signals during active operation
  a_no_x_in:  assert property (!$isunknown({serial_data, parallel_data})))
    else $error("X/Z on inputs during active operation");
  a_no_x_out: assert property (!$isunknown({shift_reg, match})))
    else $error("X/Z on outputs during active operation");

  // Coverage
  c_reset:         cover property (reset);
  c_shift_event:   cover property (past_valid && (shift_reg == { $past(shift_reg)[6:0], serial_data }));
  c_match_high:    cover property (past_valid && match);
  c_match_edge:    cover property (past_valid && !match ##1 match);
  c_match_pulse:   cover property (past_valid && !match ##1 match ##1 !match);
  c_match_reason:  cover property (past_valid && ($past(shift_reg) == parallel_data) && match);

endmodule

// Bind into the DUT (connects to internal shift_reg)
bind shift_register_comparator shift_register_comparator_sva sva (
  .clk(clk),
  .reset(reset),
  .serial_data(serial_data),
  .parallel_data(parallel_data),
  .match(match),
  .shift_reg(shift_reg)
);