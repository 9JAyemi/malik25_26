module crc8_single_bit_sva (
  input logic       data,
  input logic       enable_crc,
  input logic       reset,
  input logic       sync_reset_crc,
  input logic       clk,
  input logic [7:0] crc_out
);

  // Clock: clk
  // Reset: reset is active high and asynchronous; sync_reset_crc is a synchronous clear
  // Logic: combinational next-state CRC function driving a sequential crc_out register

  // Async reset forces the CRC output to zero.
  check_async_reset_clears_crc: assert property (
    @(posedge clk)
    reset |-> (crc_out == 8'h00)
  );

  // A sampled sync reset clears the CRC on the following cycle.
  check_sync_reset_clears_crc: assert property (
    @(posedge clk) disable iff (reset)
    sync_reset_crc |=> (crc_out == 8'h00)
  );

  // Sync reset takes priority over an enabled CRC update.
  check_sync_reset_priority_over_enable: assert property (
    @(posedge clk) disable iff (reset)
    (sync_reset_crc && enable_crc) |=> (crc_out == 8'h00)
  );

  // Without enable or sync reset, the CRC register holds its value.
  check_crc_holds_when_disabled: assert property (
    @(posedge clk) disable iff (reset)
    (!sync_reset_crc && !enable_crc) |=> (crc_out == $past(crc_out))
  );

  // Bit 0 updates with the implemented feedback equation.
  check_crc_bit0_update: assert property (
    @(posedge clk) disable iff (reset)
    (!sync_reset_crc && enable_crc) |=> (crc_out[0] == ($past(data) ^ $past(crc_out[7])))
  );

  // Bit 1 updates with the implemented feedback equation.
  check_crc_bit1_update: assert property (
    @(posedge clk) disable iff (reset)
    (!sync_reset_crc && enable_crc) |=> (crc_out[1] == ($past(data) ^ $past(crc_out[0]) ^ $past(crc_out[7])))
  );

  // Bit 2 updates with the implemented feedback equation.
  check_crc_bit2_update: assert property (
    @(posedge clk) disable iff (reset)
    (!sync_reset_crc && enable_crc) |=> (crc_out[2] == ($past(data) ^ $past(crc_out[1]) ^ $past(crc_out[7])))
  );

  // Upper CRC bits shift from the previous state when enabled.
  check_crc_upper_bits_shift: assert property (
    @(posedge clk) disable iff (reset)
    (!sync_reset_crc && enable_crc) |=> (crc_out[7:3] == $past(crc_out[6:2]))
  );

endmodule