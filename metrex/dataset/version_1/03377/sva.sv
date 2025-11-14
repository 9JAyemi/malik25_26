// Bindable SVA for UART_TX
bind UART_TX UART_TX_SVA u_uart_tx_sva();

module UART_TX_SVA;

  // Use DUT scope signals directly (via bind)
  // Clocking and past-valid
  default clocking cb @(posedge sys_clk); endclocking
  bit past_valid; initial past_valid = 0;
  always @(posedge sys_clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sample the payload when it is (legally) loaded in the DUT
  logic [7:0] load_q;
  always @(posedge sys_clk)
    if (RxD_start && (state < 4'd2)) load_q <= RxD_par;

  // 1) State legality
  a_state_legal: assert property (
    state inside {4'b0000,4'b0010,4'b0011,4'b1000,4'b1001,4'b1010,4'b1011,4'b1100,4'b1101,4'b1110,4'b1111,4'b0001}
  );

  // 2) Idle/start handshaking
  a_idle_stay:  assert property (state==4'b0000 && !(RxD_start && RTS) |=> state==4'b0000);
  a_idle_start: assert property (state==4'b0000 &&  (RxD_start && RTS) |=> state==4'b0010);

  // 3) Hold when BaudTick is low (non-idle states)
  a_hold_no_tick: assert property ((state!=4'b0000) && !BaudTick |=> state==$past(state));

  // 4) BaudTick-driven transitions
  a_sync_to_start:  assert property (state==4'b0010 && BaudTick |=> state==4'b0011);
  a_start_to_b0:    assert property (state==4'b0011 && BaudTick |=> state==4'b1000);
  a_data_inc:       assert property ((state inside {4'b1000,4'b1001,4'b1010,4'b1011,4'b1100,4'b1101,4'b1110}) && BaudTick
                                     |=> state==$past(state)+1);
  a_b7_to_stop:     assert property (state==4'b1111 && BaudTick |=> state==4'b0001);
  a_stop_to_next:   assert property (state==4'b0001 && BaudTick &&  (RxD_start && RTS) |=> state==4'b0011);
  a_stop_to_idle:   assert property (state==4'b0001 && BaudTick && !(RxD_start && RTS) |=> state==4'b0000);

  // 5) TxD_ser encoding
  a_txd_idle_high:  assert property ((state < 4'd3) |-> TxD_ser==1'b1); // idle, stop, sync
  a_txd_start_low:  assert property (state==4'b0011 |-> TxD_ser==1'b0); // start bit
  a_txd_data_match: assert property (state[3] |-> TxD_ser==RxD_buff[0]); // data states

  // 6) Buffer behavior
  a_buf_load:       assert property ((RxD_start && (state<4'd2)) |=> RxD_buff==$past(RxD_par));
  a_buf_shift:      assert property ((state[3] && BaudTick)       |=> RxD_buff==($past(RxD_buff) >> 1));
  a_buf_hold_data:  assert property ((state[3] && !BaudTick)      |=> $stable(RxD_buff));
  a_buf_hold_mid:   assert property ((state inside {4'b0010,4'b0011}) |=> $stable(RxD_buff));

  // 7) Data content mapping: bit index equals state[2:0] in data states
  a_data_map:       assert property (state[3] |-> TxD_ser == load_q[state[2:0]]);

  // 8) No X on critical regs/outs
  a_no_x:           assert property (!$isunknown({state, RxD_buff, TxD_ser}));

  // Coverage: full frame and back-to-back frames
  c_full_frame: cover property (
    state==4'b0000 && RxD_start && RTS
    ##1 state==4'b0010
    ##[1:$] (BaudTick && state==4'b0011)
    ##1 (BaudTick && state==4'b1000)
    ##1 (BaudTick && state==4'b1001)
    ##1 (BaudTick && state==4'b1010)
    ##1 (BaudTick && state==4'b1011)
    ##1 (BaudTick && state==4'b1100)
    ##1 (BaudTick && state==4'b1101)
    ##1 (BaudTick && state==4'b1110)
    ##1 (BaudTick && state==4'b1111)
    ##1 (BaudTick && state==4'b0001)
    ##1 (BaudTick && state==4'b0000)
  );

  c_back_to_back: cover property (
    state==4'b0001 && BaudTick && RxD_start && RTS ##1 state==4'b0011
    ##1 (BaudTick && state==4'b1000)
  );

  c_rts_blocked: cover property (
    state==4'b0000 && RxD_start && !RTS ##1 state==4'b0000
  );

endmodule