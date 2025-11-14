// SVA checker bound into profibus_master
bind profibus_master profibus_master_sva pmsva();

module profibus_master_sva;

  // The following names (clk, reset, state, etc.) resolve in the bound scope
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Mirror DUT encodings
  localparam int IDLE      = 0;
  localparam int TX_START  = 1;
  localparam int TX_DATA   = 2;
  localparam int RX_START  = 3;
  localparam int RX_DATA   = 4;
  localparam int BIT_TIME     = 10;
  localparam int START_DELAY  = 5;

  // Basic sanity / reset
  a_state_legal: assert property (1'b1 |-> (state inside {IDLE,TX_START,TX_DATA,RX_START,RX_DATA}));
  a_no_x:        assert property (!$isunknown({tx_busy,tx_complete,rx_data,state,bit_counter,rx_en,rx_en_int,tx_busy_int}));
  a_reset:       assert property (reset |=> state==IDLE && tx_busy==1'b0 && tx_complete==1'b0 && rx_data==8'h00 && bit_counter==4'h0);

  // Interface consistency
  a_busy_wire:   assert property (tx_busy == tx_busy_int);
  a_rxen_wire:   assert property (rx_en  == rx_en_int); // Will flag current RTL bug: rx_en never driven from rx_en_int

  // Legal one-step transitions
  a_tr_idle:     assert property ($past(state)==IDLE     |-> state inside {IDLE,TX_START});
  a_tr_txst:     assert property ($past(state)==TX_START |-> state inside {TX_START,TX_DATA});
  a_tr_txdt:     assert property ($past(state)==TX_DATA  |-> state inside {TX_DATA,RX_START});
  a_tr_rxst:     assert property ($past(state)==RX_START |-> state inside {RX_START,RX_DATA});
  a_tr_rxdt:     assert property ($past(state)==RX_DATA  |-> state inside {RX_DATA,IDLE});

  // Start of transmission handshake
  a_tx_start:    assert property ($rose(tx_en) && $past(state)==IDLE |=> state==TX_START && tx_busy);

  // tx_busy life-cycle and tx_complete relation
  a_busy_hold:   assert property ($rose(tx_busy) |=> tx_busy until_with (state==IDLE));
  a_busy_drop:   assert property ($fell(tx_busy) |-> state==IDLE && tx_complete);
  a_cmplt_only:  assert property ($rose(tx_complete) |-> $past(tx_busy) && state==IDLE && !tx_busy);

  // TX_START timing
  a_ts_begin:    assert property ($past(state)==TX_START && $past(bit_counter)==0
                                  |=> rx_en_int && bit_counter==1);
  a_ts_to_td:    assert property ($past(state)==TX_START && $past(bit_counter)==START_DELAY
                                  |=> state==TX_DATA && !rx_en_int && bit_counter==1);

  // TX_DATA timing and decision
  a_td_begin:    assert property ($past(state)==TX_DATA && $past(bit_counter)==0
                                  |=> rx_en_int && bit_counter==1);
  a_td_end_to_rs:assert property ($past(state)==TX_DATA && $past(bit_counter)==BIT_TIME && $past(tx_buffer)==8'h00
                                  |=> state==RX_START && !rx_en_int && bit_counter==1);
  a_td_end_stay: assert property ($past(state)==TX_DATA && $past(bit_counter)==BIT_TIME && $past(tx_buffer)!=8'h00
                                  |=> state==TX_DATA && !rx_en_int && bit_counter==1);

  // RX_START timing
  a_rs_begin:    assert property ($past(state)==RX_START && $past(bit_counter)==0
                                  |=> rx_en_int && bit_counter==1);
  a_rs_to_rd:    assert property ($past(state)==RX_START && $past(bit_counter)==START_DELAY
                                  |=> state==RX_DATA && !rx_en_int && bit_counter==1);

  // RX_DATA timing and decision
  a_rd_begin:    assert property ($past(state)==RX_DATA && $past(bit_counter)==0
                                  |=> bit_counter==1);
  a_rd_end_to_id:assert property ($past(state)==RX_DATA && $past(bit_counter)==BIT_TIME && $past(rx_buffer[7])
                                  |=> state==IDLE && !rx_en_int && bit_counter==1);
  a_rd_end_stay: assert property ($past(state)==RX_DATA && $past(bit_counter)==BIT_TIME && !$past(rx_buffer[7])
                                  |=> state==RX_DATA && !rx_en_int && bit_counter==1);

  // rx_data update protocol (only from IDLE path and not masked by tx_en)
  a_rx_update:   assert property ($rose(rx_complete) && $past(state)==IDLE && !$past(tx_en)
                                  |=> rx_data == $past(rx_buffer));

  // Coverage
  c_full_txrx:   cover property ($rose(tx_en) && $past(state)==IDLE
                                  ##[1:$] state==TX_START
                                  ##[1:$] state==TX_DATA
                                  ##[1:$] state==RX_START
                                  ##[1:$] state==RX_DATA
                                  ##[1:$] state==IDLE && $rose(tx_complete));

  c_rx_only:     cover property ($rose(rx_complete) && $past(state)==IDLE && !$past(tx_en)
                                  ##1 rx_data == $past(rx_buffer));

  c_hit_ts_dly:  cover property (state==TX_START && bit_counter==START_DELAY);
  c_hit_td_bit:  cover property (state==TX_DATA  && bit_counter==BIT_TIME);
  c_hit_rs_dly:  cover property (state==RX_START && bit_counter==START_DELAY);
  c_hit_rd_bit:  cover property (state==RX_DATA  && bit_counter==BIT_TIME);

  c_rxen_tog:    cover property ($changed(rx_en_int));

endmodule