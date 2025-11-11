// SVA checkers and binds for async_transmitter, async_receiver, BaudTickGen
// Focused, concise, high-quality assertions and coverage

// ----------------------------------------
// async_transmitter checker
// ----------------------------------------
module async_transmitter_sva;
  default clocking cb @(posedge clk); endclocking

  // State encoding legal set
  assert property (TxD_state inside {
    4'b0000,4'b0100,4'b1000,4'b1001,4'b1010,4'b1011,4'b1100,4'b1101,4'b1110,4'b1111,4'b0010,4'b0011
  });

  // Busy is inverse of ready
  assert property (TxD_busy == (TxD_state!=4'b0000));

  // Start when ready loads shift and enters start state
  assert property ((TxD_state==4'b0000 && TxD_start) |=> (TxD_state==4'b0100 && TxD_shift==$past(TxD_data)));

  // State transitions on BitTick
  assert property ((TxD_state==4'b0100 && BitTick) |=> TxD_state==4'b1000);
  assert property ((TxD_state==4'b1000 && BitTick) |=> TxD_state==4'b1001);
  assert property ((TxD_state==4'b1001 && BitTick) |=> TxD_state==4'b1010);
  assert property ((TxD_state==4'b1010 && BitTick) |=> TxD_state==4'b1011);
  assert property ((TxD_state==4'b1011 && BitTick) |=> TxD_state==4'b1100);
  assert property ((TxD_state==4'b1100 && BitTick) |=> TxD_state==4'b1101);
  assert property ((TxD_state==4'b1101 && BitTick) |=> TxD_state==4'b1110);
  assert property ((TxD_state==4'b1110 && BitTick) |=> TxD_state==4'b1111);
  assert property ((TxD_state==4'b1111 && BitTick) |=> TxD_state==4'b0010);
  assert property ((TxD_state==4'b0010 && BitTick) |=> TxD_state==4'b0011);
  assert property ((TxD_state==4'b0011 && BitTick) |=> TxD_state==4'b0000);

  // Hold state if no advancing condition
  assert property ((!(BitTick || (TxD_state==4'b0000 && TxD_start))) |=> $stable(TxD_state));

  // Shift behavior: right shift on data states at BitTick
  assert property ((TxD_state[3] && BitTick) |=> TxD_shift == $past(TxD_shift >> 1));

  // TxD matches intended encoding
  assert property (TxD == ((TxD_state < 4) || (TxD_state[3] && TxD_shift[0])));

  // Idle drives mark (1)
  assert property ((TxD_state==4'b0000) |-> TxD==1'b1);

  // Coverage: one full busy burst; stop states reached
  cover property ($rose(TxD_busy) ##[1:$] $fell(TxD_busy));
  cover property (BitTick && TxD_state==4'b1111 ##1 BitTick && TxD_state==4'b0011);
endmodule

bind async_transmitter async_transmitter_sva atx_sva();

// ----------------------------------------
// async_receiver checker
// ----------------------------------------
module async_receiver_sva;
  default clocking cb @(posedge clk); endclocking

`ifdef SIMULATION
  // Legal states (SIM)
  assert property (RxD_state inside {4'b0000,4'b1000,4'b1001,4'b1010,4'b1011,4'b1100,4'b1101,4'b1110,4'b1111,4'b0010});
  // Start detection (SIM)
  assert property ((RxD_state==4'b0000 && !RxD_bit) |=> RxD_state==4'b1000);
`else
  // Legal states (HW)
  assert property (RxD_state inside {4'b0000,4'b0001,4'b1000,4'b1001,4'b1010,4'b1011,4'b1100,4'b1101,4'b1110,4'b1111,4'b0010});
  // Start and mid-bit sample handoff (HW)
  assert property ((RxD_state==4'b0000 && !RxD_bit) |=> RxD_state==4'b0001);
  assert property ((RxD_state==4'b0001 && sampleNow) |=> RxD_state==4'b1000);
`endif

  // Data state progression on sampleNow
  assert property ((RxD_state==4'b1000 && sampleNow) |=> RxD_state==4'b1001);
  assert property ((RxD_state==4'b1001 && sampleNow) |=> RxD_state==4'b1010);
  assert property ((RxD_state==4'b1010 && sampleNow) |=> RxD_state==4'b1011);
  assert property ((RxD_state==4'b1011 && sampleNow) |=> RxD_state==4'b1100);
  assert property ((RxD_state==4'b1100 && sampleNow) |=> RxD_state==4'b1101);
  assert property ((RxD_state==4'b1101 && sampleNow) |=> RxD_state==4'b1110);
  assert property ((RxD_state==4'b1110 && sampleNow) |=> RxD_state==4'b1111);
  assert property ((RxD_state==4'b1111 && sampleNow) |=> RxD_state==4'b0010);
  assert property ((RxD_state==4'b0010 && sampleNow) |=> RxD_state==4'b0000);

  // Shift register behavior on each sampled data bit
  assert property ((sampleNow && RxD_state[3]) |=> RxD_data == { $past(RxD_bit), $past(RxD_data[7:1]) });

  // data_ready pulse, condition and width
  assert property ($rose(RxD_data_ready) |-> $past(sampleNow && RxD_state==4'b0010 && RxD_bit));
  assert property (RxD_data_ready |-> ##1 !RxD_data_ready);

`ifndef SIMULATION
  // endofpacket/idle consistency (lightweight)
  assert property ($rose(RxD_idle) |-> $past(RxD_state==4'b0000));
  cover property ($rose(RxD_endofpacket));
`endif

  // Coverage: one full byte reception ending in data_ready
  sequence rx_data_seq;
    sampleNow && RxD_state==4'b1000 ##1
    sampleNow && RxD_state==4'b1001 ##1
    sampleNow && RxD_state==4'b1010 ##1
    sampleNow && RxD_state==4'b1011 ##1
    sampleNow && RxD_state==4'b1100 ##1
    sampleNow && RxD_state==4'b1101 ##1
    sampleNow && RxD_state==4'b1110 ##1
    sampleNow && RxD_state==4'b1111;
  endsequence
  cover property (rx_data_seq ##1 sampleNow && RxD_state==4'b0010 ##1 RxD_data_ready);
endmodule

bind async_receiver async_receiver_sva arx_sva();

// ----------------------------------------
// BaudTickGen checker
// ----------------------------------------
module BaudTickGen_sva;
  default clocking cb @(posedge clk); endclocking

  // Tick is single-cycle high
  assert property (tick |-> !$past(tick));

  // Accumulator update rules
  assert property ( enable |=> Acc == $past(Acc[AccWidth-1:0]) + Inc );
  assert property (!enable |=> Acc == Inc);

  // Coverage: tick occurrence
  cover property (tick);
endmodule

bind BaudTickGen BaudTickGen_sva btg_sva();