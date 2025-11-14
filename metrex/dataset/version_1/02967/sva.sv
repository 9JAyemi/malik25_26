// SVA for spi_device
module spi_device_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  data_in,
  input  logic        miso,
  input  logic        mosi,
  input  logic        ready,
  input  logic [7:0]  buffer,
  input  logic [2:0]  cnt,
  input  logic [7:0]  data
);

  // Synchronous reset state
  assert property (@(posedge clk)
    reset |-> (buffer==8'h00 && cnt==3'h0 && data==8'h00 && mosi==1'b0 && ready==1'b0));

  // cnt progression: 0..6 -> +1, 7 -> 0
  assert property (@(posedge clk) disable iff (reset)
    (cnt!=3'h7) |=> (cnt == $past(cnt)+3'h1));
  assert property (@(posedge clk) disable iff (reset)
    (cnt==3'h7) |=> (cnt == 3'h0));

  // buffer updates
  assert property (@(posedge clk) disable iff (reset)
    (cnt==3'h0) |=> (buffer == $past(data_in)));
  assert property (@(posedge clk) disable iff (reset)
    (cnt inside {[3'h1:3'h6]}) |=> (buffer == { $past(buffer[6:0]), $past(mosi) }));
  assert property (@(posedge clk) disable iff (reset)
    (cnt==3'h7) |=> (buffer == { $past(buffer[6:0]), $past(miso) }));

  // mosi updates/holds
  assert property (@(posedge clk) disable iff (reset)
    (cnt!=3'h7) |=> (mosi == $past(buffer[7])));
  assert property (@(posedge clk) disable iff (reset)
    (cnt==3'h7) |=> (mosi == $past(mosi)));

  // data updates: only on cnt==7, increment by 1 (mod 256)
  assert property (@(posedge clk) disable iff (reset)
    (cnt!=3'h7) |=> (data == $past(data)));
  assert property (@(posedge clk) disable iff (reset)
    (cnt==3'h7) |=> (data == $past(data) + 8'h01));

  // ready behavior: sticky once set; only changes on cnt==7; rises only when data was 0xFF
  assert property (@(posedge clk) disable iff (reset)
    $past(ready) |-> ready);
  assert property (@(posedge clk) disable iff (reset)
    (ready != $past(ready)) |-> $past(cnt==3'h7));
  assert property (@(posedge clk) disable iff (reset)
    $rose(ready) |-> $past(cnt==3'h7 && data==8'hff));

  // Coverage
  cover property (@(posedge clk) disable iff (reset)
    (cnt==3'h0) ##1 (cnt==3'h7) ##1 (cnt==3'h0));                 // one full 8-bit transfer
  cover property (@(posedge clk) disable iff (reset)
    $rose(ready));                                                // ready asserted at least once
  cover property (@(posedge clk) disable iff (reset)
    (cnt==3'h7 && data==8'hff) ##1 (cnt==3'h0 && data==8'h00));   // data wrap after last bit

endmodule

// Bind into DUT
bind spi_device spi_device_sva sva_i (
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .miso(miso),
  .mosi(mosi),
  .ready(ready),
  .buffer(buffer),
  .cnt(cnt),
  .data(data)
);