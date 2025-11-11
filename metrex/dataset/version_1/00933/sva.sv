// SVA for TX: bind-in module, concise but covers state-machine, counters, data path, outputs

module TX_SVA;

  // Helpers
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  logic bit_tick;
  assign bit_tick = (count == 16);

  // Legal one-hot encodings
  assert property (@(posedge clk) $onehot(state)     && (state     inside {stateA,stateB,stateC,stateD,stateE}));
  assert property (@(posedge clk) $onehot(next_state) && (next_state inside {stateA,stateB,stateC,stateD,stateE}));

  // State register follows next_state
  assert property (@(posedge clk) past_valid |-> state == $past(next_state));

  // Next-state map
  assert property (@(posedge clk) state==stateA &&  tx_start |-> next_state==stateB);
  assert property (@(posedge clk) state==stateA && !tx_start |-> next_state==stateA);

  assert property (@(posedge clk) state==stateB &&  (bit_count==1) |-> next_state==stateC);
  assert property (@(posedge clk) state==stateB && !(bit_count==1) |-> next_state==stateB);

  assert property (@(posedge clk) state==stateC &&  (bit_count==9) |-> next_state==stateD);
  assert property (@(posedge clk) state==stateC && !(bit_count==9) |-> next_state==stateC);

  assert property (@(posedge clk) state==stateD &&  (bit_count==10) |-> next_state==stateE);
  assert property (@(posedge clk) state==stateD && !(bit_count==10) |-> next_state==stateD);

  assert property (@(posedge clk) state==stateE &&  tx_done |-> next_state==stateA);
  assert property (@(posedge clk) state==stateE && !tx_done |-> next_state==stateE);

  // Outputs/control per state
  assert property (@(posedge clk) state==stateA |-> (tx==1 && tx_done==1 && tick_enable==0 && rst_count==0));
  assert property (@(posedge clk) (state inside {stateB,stateC,stateD,stateE}) |-> tick_enable==1);

  // rst_count defaults high between ticks in B/C/D; tx_done low outside A or E tick
  assert property (@(posedge clk) state==stateB && !bit_tick |-> (rst_count==1 && tx_done==0));
  assert property (@(posedge clk) state==stateC && !bit_tick |-> rst_count==1);
  assert property (@(posedge clk) state==stateD && !bit_tick |-> rst_count==1);
  assert property (@(posedge clk) !(state==stateA || (state==stateE && bit_tick)) |-> tx_done==0);

  // Bit-tick actions on clk domain
  // Start bit
  assert property (@(posedge clk) state==stateB && bit_tick |-> (tx==0 && rst_count==0));
  assert property (@(posedge clk) state==stateB && bit_tick |=> (bit_count==$past(bit_count)+1) && (d_aux==$past(d_in)));

  // Data bits (LSB-first) and shift
  assert property (@(posedge clk) state==stateC && bit_tick |=> (tx==$past(d_aux[0])) && (bit_count==$past(bit_count)+1) && (rst_count==0));
  assert property (@(posedge clk) state==stateC && bit_tick |=> d_aux == {1'b0, $past(d_aux[7:1])});

  // Stop bit
  assert property (@(posedge clk) state==stateD && bit_tick |-> (tx==1 && rst_count==0));
  assert property (@(posedge clk) state==stateD && bit_tick |=> (bit_count==$past(bit_count)+1));

  // Done and bit_count clear
  assert property (@(posedge clk) state==stateE && bit_tick |-> tx_done==1);
  assert property (@(posedge clk) state==stateE && bit_tick |=> bit_count==0);

  // tx stable between baud ticks while active
  assert property (@(posedge clk) (state inside {stateB,stateC,stateD,stateE}) && !bit_tick |-> $stable(tx));

  // Baud-rate counter behavior (baud clock domain)
  assert property (@(posedge baud_rate) !rst_count |-> count==0);
  assert property (@(posedge baud_rate)  rst_count &&  tick_enable |=> count == $past(count)+1);
  assert property (@(posedge baud_rate)  rst_count && !tick_enable |=> count == $past(count));

  // Boundary transitions at programmed counts
  assert property (@(posedge clk) state==stateB && (bit_count==1)  |-> next_state==stateC);
  assert property (@(posedge clk) state==stateC && (bit_count==9)  |-> next_state==stateD);
  assert property (@(posedge clk) state==stateD && (bit_count==10) |-> next_state==stateE);
  assert property (@(posedge clk) state==stateE && bit_tick       |-> next_state==stateA);

  // Full-frame coverage: start->8 data->stop->done->idle
  cover property (@(posedge clk)
    (state==stateB && bit_tick)
    ##1 (state==stateC && bit_tick)[*8]
    ##1 (state==stateD && bit_tick)
    ##1 (state==stateE && bit_tick)
    ##1 (state==stateA && tx==1 && tx_done==1));

  // Data bit value coverage
  cover property (@(posedge clk) state==stateC && bit_tick && $past(d_aux[0])==1'b0);
  cover property (@(posedge clk) state==stateC && bit_tick && $past(d_aux[0])==1'b1);

endmodule

bind TX TX_SVA tx_sva();