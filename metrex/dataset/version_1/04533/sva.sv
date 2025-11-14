// SVA for uart_tx — bindable checker
module uart_tx_sva;

  // Bind-time visibility into DUT scope (clk_i, state, tx_ctr, s_rx, s_tx, rx_i, rx_i_v, tx_o, tx_o_v, ST_*).
  default clocking cb @(posedge clk_i); endclocking
  default disable iff ($initstate);

  // Basic invariants
  assert property (state inside {ST_IDLE, ST_START, ST_DATA, ST_STOP});
  assert property (tx_o_v == (state != ST_IDLE));
  assert property (tx_o == s_tx);

  // FSM transitions
  assert property ((state==ST_IDLE && rx_i_v) |=> state==ST_START);
  assert property (state==ST_START |=> state==ST_DATA);
  assert property ((state==ST_DATA && tx_ctr!=7) |=> state==ST_DATA);
  assert property ((state==ST_DATA && tx_ctr==7) |=> state==ST_STOP);
  assert property (state==ST_STOP |=> state==ST_IDLE);

  // Reverse transition legality
  assert property ((state==ST_START) |-> $past(state)==ST_IDLE);
  assert property ((state==ST_DATA)  |-> $past(state) inside {ST_START, ST_DATA});
  assert property ((state==ST_STOP)  |-> ($past(state)==ST_DATA && $past(tx_ctr)==7));

  // Counter behavior
  assert property ((state!=ST_DATA) |-> tx_ctr==0);
  assert property ((state==ST_DATA && $past(state)!=ST_DATA) |-> tx_ctr==1);
  assert property ((state==ST_DATA && $past(state)==ST_DATA) |-> tx_ctr==$past(tx_ctr)+1);

  // Shift register behavior
  assert property (state==ST_START |-> s_rx==rx_i);
  assert property ((state==ST_DATA && $past(state)==ST_START) |-> s_rx==($past(rx_i)>>1));
  assert property ((state==ST_DATA && $past(state)==ST_DATA)  |-> s_rx==($past(s_rx)>>1));

  // Output encoding per state
  assert property (state==ST_IDLE  |-> tx_o==1);
  assert property (state==ST_START |-> tx_o==0);
  assert property (state==ST_DATA  |-> tx_o==s_rx[0]);
  assert property (state==ST_STOP  |-> tx_o==1);

  // End-to-end UART frame: start(0), 8 data LSB->MSB, stop(1)
  property p_frame_seq;
    logic [7:0] d;
    (state==ST_IDLE && rx_i_v, d=rx_i)
    ##1 (state==ST_START && tx_o==0 && tx_o_v)
    ##1 (state==ST_DATA  && tx_o==d[0] && tx_o_v)
    ##1 (state==ST_DATA  && tx_o==d[1] && tx_o_v)
    ##1 (state==ST_DATA  && tx_o==d[2] && tx_o_v)
    ##1 (state==ST_DATA  && tx_o==d[3] && tx_o_v)
    ##1 (state==ST_DATA  && tx_o==d[4] && tx_o_v)
    ##1 (state==ST_DATA  && tx_o==d[5] && tx_o_v)
    ##1 (state==ST_DATA  && tx_o==d[6] && tx_o_v)
    ##1 (state==ST_DATA  && tx_o==d[7] && tx_o_v)
    ##1 (state==ST_STOP  && tx_o==1 && tx_o_v)
    ##1 (state==ST_IDLE  && !tx_o_v);
  endproperty
  assert property (p_frame_seq);

  // Compact equivalence: busy window is exactly 10 cycles after accept
  assert property ((state==ST_IDLE && rx_i_v) |=> (state!=ST_IDLE)[*10] ##1 state==ST_IDLE);

  // Coverage
  cover property ((state==ST_IDLE && rx_i_v)
                  ##1 state==ST_START
                  ##1 (state==ST_DATA)[*8]
                  ##1 state==ST_STOP
                  ##1 state==ST_IDLE);

  cover property ((state==ST_IDLE && rx_i_v && rx_i==8'h00) ##1 (state==ST_STOP));
  cover property ((state==ST_IDLE && rx_i_v && rx_i==8'hFF) ##1 (state==ST_STOP));

endmodule

bind uart_tx uart_tx_sva u_uart_tx_sva();