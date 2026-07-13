module shift_register_sva (
  input logic clk,
  input logic shift_enable,
  input logic parallel_load_enable,
  input logic [15:0] data_in,
  input logic [15:0] data_out
);
  // Clock: clk (posedge). No reset. Sequential register: parallel load > else shift-left with 0 fill > else hold.

  // Parallel load updates data_out on the next cycle to current data_in.
  load_updates_next: assert property (
    @(posedge clk) parallel_load_enable |=> (data_out == $past(data_in,1,data_in))
  );

  // Shift-left by one with zero fill when shifting without load.
  shift_vector_update: assert property (
    @(posedge clk) (!parallel_load_enable && shift_enable) |=> (data_out == { $past(data_out,1,data_out)[14:0], 1'b0 })
  );

  // LSB becomes 0 on shift (no load).
  shift_lsb_zero: assert property (
    @(posedge clk) (!parallel_load_enable && shift_enable) |=> (data_out[0] == 1'b0)
  );

  // MSB becomes prior bit14 on shift (no load).
  shift_msb_from_bit14: assert property (
    @(posedge clk) (!parallel_load_enable && shift_enable) |=> (data_out[15] == $past(data_out,1,data_out)[14])
  );

  // Hold value when neither load nor shift is enabled.
  hold_when_idle: assert property (
    @(posedge clk) (!parallel_load_enable && !shift_enable) |=> (data_out == $past(data_out,1,data_out))
  );

  // Load has priority over shift when both are asserted.
  load_over_shift_priority: assert property (
    @(posedge clk) (parallel_load_enable && shift_enable) |=> (data_out == $past(data_in,1,data_in))
  );

  // Any change in data_out must be caused by a load or shift in the previous cycle.
  change_requires_enable: assert property (
    @(posedge clk) (data_out != $past(data_out,1,data_out)) |-> $past(parallel_load_enable || shift_enable,1,1'b0)
  );

  // Sixteen consecutive shifts with no load clear the register to zero.
  sixteen_shifts_clear_to_zero: assert property (
    @(posedge clk) (!parallel_load_enable && shift_enable)[*16] |=> (data_out == 16'h0000)
  );

endmodule