module shift_register_sva (
  input logic clk,
  input logic reset,
  input logic serial_in,
  input logic serial_out,
  input logic [31:0] parallel_out
);

  ///// Reset behavior /////
  // While reset is asserted, outputs are driven to zero.
  check_reset_clears_outputs: assert property (
    @(posedge clk) reset |-> (parallel_out == 32'b0) && (serial_out == 1'b0)
  );

  // If reset stays asserted across cycles, outputs remain zero.
  check_reset_holds_zero: assert property (
    @(posedge clk) $past(reset) && reset |-> (parallel_out == 32'b0) && (serial_out == 1'b0)
  );

  // On reset deassertion edge, only LSB captures prior serial_in; MSB stays 0.
  check_first_cycle_after_reset_deassert: assert property (
    @(posedge clk) $fell(reset) |-> (parallel_out == {31'b0, $past(serial_in)}) && (serial_out == 1'b0)
  );

  ///// Structural relations /////
  // serial_out always mirrors MSB of parallel_out.
  check_serial_out_matches_msb: assert property (
    @(posedge clk) disable iff (reset) (serial_out == parallel_out[31])
  );

  ///// Shift behavior /////
  // Next parallel_out equals prior parallel_out left-shifted with prior serial_in at LSB.
  check_shift_update_full: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (parallel_out == { $past(parallel_out[30:0]), $past(serial_in) })
  );

  // MSB updates from prior bit[30] when shifting.
  check_msb_updates_from_bit30: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (parallel_out[31] == $past(parallel_out[30]))
  );

  // LSB captures prior serial_in when shifting.
  check_lsb_captures_serial_in: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (parallel_out[0] == $past(serial_in))
  );

  // Middle bits [30:1] shift up from prior [29:0].
  check_middle_bits_shift: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (parallel_out[30:1] == $past(parallel_out[29:0]))
  );

  // serial_out equals prior bit[30] after a shift.
  check_serial_out_from_prior_bit30: assert property (
    @(posedge clk) disable iff (reset) $past(!reset) |-> (serial_out == $past(parallel_out[30]))
  );

endmodule