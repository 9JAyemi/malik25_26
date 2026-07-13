module shift_register_sva (
  input logic clk,
  input logic load,
  input logic [3:0] data_in,
  input logic reset,
  input logic [3:0] data_out
);
  // Clock: clk (posedge). Reset: reset (active-high, synchronous). Logic: sequential with load/shift; data_out mirrors shift_reg.

  // Reset sets register to 0 on the next cycle.
  reset_clears: assert property (
    @(posedge clk) reset |=> (data_out == 4'b0000)
  );

  // Reset overrides load when both are asserted.
  reset_overrides_load: assert property (
    @(posedge clk) (reset && load) |=> (data_out == 4'b0000)
  );

  // Load captures data_in on the next cycle (when not in reset).
  load_writes_next: assert property (
    @(posedge clk) disable iff (reset) load |=> (data_out == $past(data_in))
  );

  // Shift operation: next value is {prev[2:0], 1'b0} when not loading.
  shift_next_value: assert property (
    @(posedge clk) disable iff (reset) !load |=> (data_out == { $past(data_out[2:0]), 1'b0 })
  );

  // Shift LSB becomes 0.
  shift_lsb_zero: assert property (
    @(posedge clk) disable iff (reset) !load |=> (data_out[0] == 1'b0)
  );

  // Shift moves bit0 to bit1.
  shift_bit1_from_bit0: assert property (
    @(posedge clk) disable iff (reset) !load |=> (data_out[1] == $past(data_out[0]))
  );

  // Shift moves bit1 to bit2.
  shift_bit2_from_bit1: assert property (
    @(posedge clk) disable iff (reset) !load |=> (data_out[2] == $past(data_out[1]))
  );

  // Shift moves bit2 to bit3.
  shift_bit3_from_bit2: assert property (
    @(posedge clk) disable iff (reset) !load |=> (data_out[3] == $past(data_out[2]))
  );

  // After 4 consecutive shifts (no load), the register becomes 0.
  four_shifts_zero: assert property (
    @(posedge clk) disable iff (reset) (!load)[*4] |=> (data_out == 4'b0000)
  );

  // A load followed by a shift brings loaded bit2 to MSB two cycles later.
  load_then_shift_moves_loaded_bit2_to_msb: assert property (
    @(posedge clk) disable iff (reset) (load ##1 !load) |=> (data_out[3] == $past(data_in[2], 2))
  );

endmodule