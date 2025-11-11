// SVA for shift_register_16bit
module shift_register_16bit_sva (
  input  logic        clk,
  input  logic        resetn,
  input  logic        parallel_load,
  input  logic        serial_in,
  input  logic        serial_out,
  ref    logic [15:0] shift_reg
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn)

  // Structural tie-off
  assert property (serial_out == shift_reg[15]);

  // Reset behavior (checked even during reset)
  assert property (@(posedge clk) !resetn |-> shift_reg == 16'h0000);

  // Parallel load semantics (1-bit into 16-bit => zero-extended)
  assert property (parallel_load |=> shift_reg == {15'b0, serial_in});
  assert property (parallel_load |=> serial_out == 1'b0);

  // Shift-left with 0 fill
  assert property (!parallel_load |=> shift_reg == { $past(shift_reg)[14:0], 1'b0 });
  // MSB after shift equals previous bit[14]
  assert property (!parallel_load |=> serial_out == $past(shift_reg[14]));

  // After 16 consecutive shifts (no loads), register clears to zero
  assert property ((!parallel_load)[*16] |=> shift_reg == 16'h0000);

  // No X/Z after reset released
  assert property (!$isunknown({shift_reg, serial_out}));

  // Coverage
  cover property ($fell(resetn));
  cover property ($rose(resetn));
  cover property (parallel_load &&  serial_in);
  cover property (parallel_load && !serial_in);
  cover property (!parallel_load);
  // Load 1 into bit0, propagate to MSB in 15 shifts
  cover property (parallel_load && serial_in ##1 (!parallel_load)[*15] ##1 serial_out);
  // 16 shifts lead to zero
  cover property ((!parallel_load)[*16] ##1 shift_reg == 16'h0000);

endmodule

// Bind into the DUT
bind shift_register_16bit shift_register_16bit_sva sva_i (
  .clk(clk),
  .resetn(resetn),
  .parallel_load(parallel_load),
  .serial_in(serial_in),
  .serial_out(serial_out),
  .shift_reg(shift_reg)
);