// SimpleUART SVA checker (bind into DUT scope)
// Usage: bind simpleuart simpleuart_sva();

module simpleuart_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn);

  // Basic combinational mirrors
  assert property (ser_tx == send_pattern[0]);
  assert property (reg_div_do == cfg_divider);
  assert property (reg_dat_wait == (reg_dat_we && (send_bitcnt != 0 || send_dummy)));

  // reg_dat_do formatting
  assert property ( recv_buf_valid |-> (reg_dat_do == {24'h0, recv_buf_data}) );
  assert property ( !recv_buf_valid |-> (reg_dat_do == 32'hFFFF_FFFF) );

  // Divider byte writes (write-hit updates, no-write holds)
  assert property ( reg_div_we[0] |=> cfg_divider[ 7: 0] == $past(reg_div_di[ 7: 0]) );
  assert property ( reg_div_we[1] |=> cfg_divider[15: 8] == $past(reg_div_di[15: 8]) );
  assert property ( reg_div_we[2] |=> cfg_divider[23:16] == $past(reg_div_di[23:16]) );
  assert property ( reg_div_we[3] |=> cfg_divider[31:24] == $past(reg_div_di[31:24]) );
  assert property ( !reg_div_we[0] |=> cfg_divider[ 7: 0] == $past(cfg_divider[ 7: 0]) );
  assert property ( !reg_div_we[1] |=> cfg_divider[15: 8] == $past(cfg_divider[15: 8]) );
  assert property ( !reg_div_we[2] |=> cfg_divider[23:16] == $past(cfg_divider[23:16]) );
  assert property ( !reg_div_we[3] |=> cfg_divider[31:24] == $past(cfg_divider[31:24]) );

  // RX: idle state behavior
  assert property ( recv_state == 0 |-> recv_divcnt == 0 );
  assert property ( recv_state == 0 && ser_rx == 1'b1 |=> recv_state == 0 );

  // RX: start-bit mid-sample transition
  assert property ( recv_state == 1 && (2*recv_divcnt > cfg_divider)
                    |=> (recv_state == 2 && recv_divcnt == 0) );

  // RX: data-bit sampling and shift (states 2..9)
  assert property ( (recv_state inside {[2:9]}) && (recv_divcnt > cfg_divider)
                    |=> (recv_state == $past(recv_state)+1 &&
                         recv_divcnt == 0 &&
                         recv_pattern[6:0] == $past(recv_pattern[7:1]) &&
                         recv_pattern[7]   == $past(ser_rx)) );

  // RX: stop-bit wait and byte latch
  assert property ( recv_state == 10 && (recv_divcnt > cfg_divider)
                    |=> (recv_state == 0 && recv_buf_valid && recv_buf_data == $past(recv_pattern)) );

  // RX: recv_buf_valid protocol
  assert property ( reg_dat_re |=> !recv_buf_valid );
  assert property ( (! $past(recv_buf_valid)) && recv_buf_valid
                    |-> ($past(recv_state) == 10 && $past(recv_divcnt) > $past(cfg_divider)) );

  // TX: idle line high
  assert property ( send_bitcnt == 0 |-> ser_tx == 1'b1 );

  // TX: load data when idle (no dummy)
  assert property ( reg_dat_we && (send_bitcnt == 0) && !send_dummy
                    |=> (send_pattern == {1'b1, $past(reg_dat_di[7:0]), 1'b0} &&
                         send_bitcnt  == 10 &&
                         send_divcnt  == 0 &&
                         ser_tx       == 1'b0) );

  // TX: dummy burst entry
  assert property ( send_dummy && (send_bitcnt == 0)
                    |=> (send_pattern == 10'h3FF && send_bitcnt == 15 && send_divcnt == 0 && ser_tx == 1'b1) );

  // TX: shift on baud tick
  assert property ( (send_bitcnt > 0) && (send_divcnt > cfg_divider)
                    |=> (send_pattern == {1'b1, $past(send_pattern[9:1])} &&
                         send_bitcnt  == $past(send_bitcnt) - 1 &&
                         send_divcnt  == 0) );

  // TX: hold between baud ticks
  assert property ( (send_bitcnt > 0) && !(send_divcnt > cfg_divider)
                    |=> (send_pattern == $past(send_pattern) &&
                         send_bitcnt  == $past(send_bitcnt)) );

  // Coverage

  // Cover: Divider write triggers a dummy burst and completes
  cover property ( reg_div_we ##1 (send_dummy && (send_bitcnt == 0))
                   ##1 (send_bitcnt == 15) ##[1:$] (send_bitcnt == 0) );

  // Cover: TX data write issues start bit and completes frame
  cover property ( reg_dat_we && (send_bitcnt == 0) && !send_dummy
                   ##1 (ser_tx == 1'b0 && send_bitcnt == 10)
                   ##[1:$] (send_bitcnt == 0 && ser_tx == 1'b1) );

  // Cover: RX full byte reception and readout
  cover property ( (recv_state == 0 && ser_rx == 1'b0)
                   ##1 (recv_state == 1)
                   ##[1:$] (recv_state == 10)
                   ##1 (recv_buf_valid) ##1 reg_dat_re && !recv_buf_valid );

  // Cover: reg_dat_wait asserted when trying to write while busy
  cover property ( (send_bitcnt != 0 || send_dummy) && reg_dat_we ##0 reg_dat_wait );

endmodule

bind simpleuart simpleuart_sva;