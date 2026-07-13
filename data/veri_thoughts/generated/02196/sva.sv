module shift_register_sva (
  input  logic        clk,
  input  logic        reset,      // active-high synchronous reset
  input  logic        shift_in,
  input  logic        shift,
  input  logic        shift_out,
  input  logic [15:0] data
);
  // On the cycle after reset was high, data and shift_out are cleared to 0.
  check_reset_clears_state: assert property (
    @(posedge clk) disable iff (reset)
      $past(reset) |-> (data == 16'h0) && (shift_out == 1'b0)
  );

  // When shifting (and not in reset in the previous cycle), data shifts left with new LSB from shift_in.
  check_shift_updates_data: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset && shift) |-> (data == { $past(data[14:0]), $past(shift_in) })
  );

  // When shifting (and not in reset in the previous cycle), shift_out equals previous MSB of data.
  check_shift_updates_shift_out: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset && shift) |-> (shift_out == $past(data[15]))
  );

  // Without shift (and not in reset in the previous cycle), data holds its value.
  check_hold_data_without_shift: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset && !shift) |-> (data == $past(data))
  );

  // Without shift (and not in reset in the previous cycle), shift_out holds its value.
  check_hold_shiftout_without_shift: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset && !shift) |-> (shift_out == $past(shift_out))
  );

  // On shift, new MSB of data comes from previous bit14.
  check_data_msb_from_prev_bit14: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset && shift) |-> (data[15] == $past(data[14]))
  );

  // On shift, new LSB of data comes from previous shift_in.
  check_data_lsb_from_shiftin: assert property (
    @(posedge clk) disable iff (reset)
      $past(!reset && shift) |-> (data[0] == $past(shift_in))
  );

  // Reset takes precedence over shift when both were high in the previous cycle.
  check_reset_overrides_shift: assert property (
    @(posedge clk) disable iff (reset)
      $past(reset && shift) |-> (data == 16'h0) && (shift_out == 1'b0)
  );
endmodule