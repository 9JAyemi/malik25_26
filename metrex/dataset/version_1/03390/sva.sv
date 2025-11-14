// SVA checker for AvalonBusInterface
module AvalonBusInterface_sva (
  input  logic        clk, rst,
  input  logic [31:0] bus_addr,
  input  logic        bus_read, bus_write,
  input  logic [31:0] bus_read_data,
  input  logic        bus_ack,
  input  logic [31:0] audio_fifo_address,
  input  logic [31:0] audio_left_address,
  input  logic [31:0] audio_right_address,
  input  logic [31:0] counter
);

  // Synchronous reset clears registers next cycle
  assert property (@(posedge clk)
    rst |=> (bus_ack==1'b0 && bus_read_data==32'b0 && counter==32'b0));

  // Address constants must match spec
  assert property (@(posedge clk) audio_fifo_address == 32'h0000_3044);
  assert property (@(posedge clk) audio_left_address  == 32'h0000_3048);
  assert property (@(posedge clk) audio_right_address == 32'h0000_304C);

  // Ack mirrors read|write (registered)
  assert property (@(posedge clk) disable iff (rst)
    bus_ack == $past(bus_read || bus_write));

  // bus_read_data may change only due to reads of supported addresses
  assert property (@(posedge clk) disable iff (rst)
    (bus_read_data != $past(bus_read_data))
      |-> $past(bus_read && ((bus_addr==audio_fifo_address) || (bus_addr==audio_right_address))));

  // Write-only cycles must not change read_data
  assert property (@(posedge clk) disable iff (rst)
    $past(bus_write && !bus_read) |-> (bus_read_data == $past(bus_read_data)));

  // Read of unsupported address must not change read_data
  assert property (@(posedge clk) disable iff (rst)
    $past(bus_read && (bus_addr!=audio_fifo_address) && (bus_addr!=audio_right_address))
      |-> (bus_read_data == $past(bus_read_data)));

  // FIFO status read returns constant 0x03000002 (registered)
  assert property (@(posedge clk) disable iff (rst)
    $past(bus_read && (bus_addr==audio_fifo_address))
      |-> (bus_read_data == 32'h0300_0002));

  // Right-channel data read returns previous counter value (registered)
  assert property (@(posedge clk) disable iff (rst)
    $past(bus_read && (bus_addr==audio_right_address))
      |-> (bus_read_data == $past(counter)));

  // Counter increments only on right-channel read
  assert property (@(posedge clk) disable iff (rst)
    $past(bus_read && (bus_addr==audio_right_address))
      |-> (counter == $past(counter)+32'd1));

  // Counter stable otherwise
  assert property (@(posedge clk) disable iff (rst)
    $past(!(bus_read && (bus_addr==audio_right_address)))
      |-> (counter == $past(counter)));

  // Basic functional coverage
  cover property (@(posedge clk) bus_read && (bus_addr==audio_fifo_address));
  cover property (@(posedge clk) bus_read && (bus_addr==audio_right_address));
  cover property (@(posedge clk) bus_read && (bus_addr!=audio_fifo_address) && (bus_addr!=audio_right_address));
  cover property (@(posedge clk) bus_write && !bus_read);
  cover property (@(posedge clk) bus_read && bus_write);
  cover property (@(posedge clk) disable iff (rst)
    (bus_read && (bus_addr==audio_right_address)) ##1 (bus_read && (bus_addr==audio_right_address)));
  cover property (@(posedge clk) rst ##1 !rst ##1 (bus_read && (bus_addr==audio_right_address)));
endmodule

// Bind into DUT (connects to internals for stronger checking)
bind AvalonBusInterface AvalonBusInterface_sva u_avalonBusInterface_sva (
  .clk               (clk),
  .rst               (rst),
  .bus_addr          (bus_addr),
  .bus_read          (bus_read),
  .bus_write         (bus_write),
  .bus_read_data     (bus_read_data),
  .bus_ack           (bus_ack),
  .audio_fifo_address(audio_fifo_address),
  .audio_left_address(audio_left_address),
  .audio_right_address(audio_right_address),
  .counter           (counter)
);