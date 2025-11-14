// SVA checkers for async_transmitter and async_receiver
// Bind these into the DUTs; no DUT/TB code needed beyond bind statements.

module async_transmitter_sva(
  input  logic        clk,
  input  logic        TxD_start,
  input  logic [7:0]  TxD_data,
  input  logic        TxD,
  input  logic        TxD_busy,
  input  logic        BitTick,
  input  logic [3:0]  TxD_state,
  input  logic [7:0]  TxD_shift
);
  default clocking @(posedge clk); endclocking

  // Busy/ready/state/line relationships
  assert property (TxD_busy == (TxD_state != 4'h0));
  assert property (TxD_state==4'h4 |-> TxD==1'b0); // start bit forced low
  assert property ((TxD_state inside {4'h0,4'h2,4'h3}) |-> TxD==1'b1); // idle + 2 stop bits high
  assert property (TxD_state[3] |-> (TxD === TxD_shift[0])); // data bits from LSB

  // State sequencing on BitTick
  assert property ((TxD_state==4'h0 && TxD_start) |=> (TxD_state==4'h4 && TxD_busy));
  assert property ((TxD_state==4'h4 && BitTick) |=> (TxD_state==4'h8));
  assert property (((TxD_state inside {[4'h8:4'hE]}) && BitTick) |=> (TxD_state == $past(TxD_state) + 4'h1));
  assert property ((TxD_state==4'hF && BitTick) |=> (TxD_state==4'h2));
  assert property ((TxD_state==4'h2 && BitTick) |=> (TxD_state==4'h3));
  assert property ((TxD_state==4'h3 && BitTick) |=> (TxD_state==4'h0 && !TxD_busy));

  // Shift register behavior
  assert property ((TxD_state==4'h0 && TxD_start) |=> (TxD_shift == $past(TxD_data)));
  assert property ((TxD_state[3] && BitTick) |=> (TxD_shift == $past(TxD_shift >> 1)));
  assert property (!((TxD_state==4'h0 && TxD_start) || (TxD_state[3] && BitTick)) |-> $stable(TxD_shift));

`ifndef SIMULATION
  // In synth mode, ticks only while busy
  assert property (!TxD_busy |-> !BitTick);
`endif

  // Concise coverage: a full frame completes; interesting data patterns start
  cover property ((TxD_state==4'h0 && TxD_start) ##1 TxD_busy ##[1:$] !TxD_busy);
  cover property (TxD_state==4'h0 && TxD_start && TxD_data==8'h00);
  cover property (TxD_state==4'h0 && TxD_start && TxD_data==8'hFF);
endmodule

bind async_transmitter async_transmitter_sva
(
  .clk(clk),
  .TxD_start(TxD_start),
  .TxD_data(TxD_data),
  .TxD(TxD),
  .TxD_busy(TxD_busy),
  .BitTick(BitTick),
  .TxD_state(TxD_state),
  .TxD_shift(TxD_shift)
);


module async_receiver_sva(
  input  logic        clk,
  input  logic        RxD,
  input  logic        RxD_idle,
  input  logic        RxD_data_ready,
  input  logic [7:0]  RxD_data,
  input  logic        RxD_endofpacket,
  input  logic [3:0]  RxD_state,
  input  logic        RxD_bit,
  input  logic        sampleNow
);
  default clocking @(posedge clk); endclocking

  // Idle only when state==0; EOP only in idle and not yet idle-flagged
  assert property (RxD_idle |-> RxD_state==4'h0);
  assert property (RxD_state!=4'h0 |-> !RxD_idle);
  assert property (RxD_endofpacket |-> (!RxD_idle && RxD_state==4'h0));

  // Data ready is a 1-cycle pulse and happens on stop sample
  assert property (RxD_data_ready |=> !RxD_data_ready);
  assert property (RxD_data_ready |-> (sampleNow && RxD_state==4'h2 && RxD_bit));

  // State sequencing on sampleNow
`ifdef SIMULATION
  assert property ((RxD_state==4'h0 && !RxD_bit) |=> (RxD_state==4'h8));
`else
  assert property ((RxD_state==4'h0 && !RxD_bit) |=> (RxD_state==4'h1));
  assert property ((RxD_state==4'h1 && sampleNow) |=> (RxD_state==4'h8));
`endif
  assert property (((RxD_state inside {[4'h8:4'hE]}) && sampleNow) |=> (RxD_state == $past(RxD_state) + 4'h1));
  assert property ((RxD_state==4'hF && sampleNow) |=> (RxD_state==4'h2));
  assert property ((RxD_state==4'h2 && sampleNow) |=> (RxD_state==4'h0));

  // Shift behavior: shift only on data sampling
  assert property ((sampleNow && RxD_state[3]) |=> (RxD_data == { $past(RxD_bit), $past(RxD_data[7:1]) }));
  assert property (!(sampleNow && RxD_state[3]) |-> $stable(RxD_data));

  // Coverage: byte received; idle gap observed
  cover property (RxD_data_ready);
  cover property (RxD_idle ##1 !RxD_idle ##[1:$] RxD_idle); // gap across a frame
endmodule

bind async_receiver async_receiver_sva
(
  .clk(clk),
  .RxD(RxD),
  .RxD_idle(RxD_idle),
  .RxD_data_ready(RxD_data_ready),
  .RxD_data(RxD_data),
  .RxD_endofpacket(RxD_endofpacket),
  .RxD_state(RxD_state),
  .RxD_bit(RxD_bit),
  .sampleNow(sampleNow)
);