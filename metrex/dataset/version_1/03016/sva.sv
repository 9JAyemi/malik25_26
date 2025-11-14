// SVA checker for uart_transceiver
// Bind into the DUT or include inside the module for direct use.

module uart_transceiver_sva();

  // Use DUT scope via bind; no ports needed.
  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (sys_rst);

  // --------------------
  // Assumptions (protocol/config)
  // --------------------
  // Valid baud divisor and stable while active
  assume property (divisor > 16'd1);
  assume property ((rx_busy || tx_busy) |-> $stable(divisor));
  // No write while transmitter busy (single-entry TX)
  assume property (tx_wr |-> !tx_busy);

  // --------------------
  // Baud-tick generator (enable16)
  // --------------------
  assert property (enable16 == (enable16_counter == 16'd0));
  assert property (!enable16 |=> enable16_counter == $past(enable16_counter) - 16'd1);
  assert property ( enable16 |=> enable16_counter == divisor - 16'd1);
  assert property (disable iff (1'b0) sys_rst |-> enable16_counter == divisor - 16'd1);

  // --------------------
  // RX input synchronizer
  // --------------------
  assert property (uart_rx1 == $past(uart_rx));
  assert property (uart_rx2 == $past(uart_rx1));
  assert property (enable16 |=> uart_rx_r == $past(uart_rx2));

  // --------------------
  // RX path
  // --------------------
  // State holds between ticks
  assert property (!enable16 |=> $stable(rx_busy) && $stable(rx_count16) && $stable(rx_bitcount) && $stable(rx_reg));

  // Start-bit detect (falling edge sampled at tick)
  assert property (enable16 && !rx_busy && (~uart_rx2 & uart_rx_r)
                   |=> rx_busy && rx_count16 == 4'd7 && rx_bitcount == 4'd0);

  // 16x counter and bit counter progression while busy
  assert property (enable16 && rx_busy |=> rx_count16 == $past(rx_count16) + 4'd1);
  assert property (enable16 && rx_busy && rx_count16 == 4'd0
                   |=> rx_bitcount == $past(rx_bitcount) + 4'd1);

  // False start (invalid start mid-sample)
  assert property (enable16 && rx_busy && rx_count16 == 4'd0 && rx_bitcount == 4'd0 && uart_rx2
                   |=> !rx_busy);

  // Data bit shift (bits 1..8), LSB first
  assert property (enable16 && rx_busy && rx_count16 == 4'd0 && (rx_bitcount inside {[4'd1:4'd8]})
                   |=> rx_reg == {uart_rx2, $past(rx_reg[7:1])});

  // Stop bit handling and completion
  assert property (enable16 && rx_busy && rx_count16 == 4'd0 && rx_bitcount == 4'd9
                   |=> !rx_busy);
  assert property (enable16 && rx_busy && rx_count16 == 4'd0 && rx_bitcount == 4'd9 && uart_rx2
                   |=> rx_done && rx_data == $past(rx_reg));
  assert property (enable16 && rx_busy && rx_count16 == 4'd0 && rx_bitcount == 4'd9 &&
                   !uart_rx2 && $past(rx_reg) == 8'h00
                   |=> break);

  // One-cycle pulses and causality
  assert property (rx_done |=> !rx_done);
  assert property (break   |=> !break);
  assert property (rx_done |-> $past(enable16 && rx_busy && rx_count16 == 4'd0 && rx_bitcount == 4'd9 && uart_rx2));
  assert property (rx_done |-> !rx_busy);

  // --------------------
  // TX path
  // --------------------
  // Idle high when not transmitting (and no new write)
  assert property (!tx_busy && !tx_wr |-> uart_tx);

  // Write kicks off start bit immediately and initializes counters/shift-reg
  assert property (tx_wr |=> tx_busy && (uart_tx == 1'b0) &&
                           tx_bitcount == 4'd0 && tx_count16 == 4'd1 &&
                           tx_reg == tx_data);

  // Hold state between ticks (no new write)
  assert property (tx_busy && !enable16 && !tx_wr |=> $stable(tx_count16) && $stable(tx_bitcount));

  // 16x counter progression while busy
  assert property (enable16 && tx_busy |=> tx_count16 == $past(tx_count16) + 4'd1);

  // Data bits shift out LSB-first on bit boundaries (bitcount 0..7)
  assert property (enable16 && tx_busy && tx_count16 == 4'd0 && (tx_bitcount inside {[4'd0:4'd7]})
                   |=> (uart_tx == $past(tx_reg[0])) &&
                       (tx_reg  == {1'b0, $past(tx_reg[7:1])}));

  // Stop bit high at bitcount 8, complete at 9 with done pulse and busy deassert
  assert property (enable16 && tx_busy && tx_count16 == 4'd0 && tx_bitcount == 4'd8
                   |=> uart_tx == 1'b1);
  assert property (enable16 && tx_busy && tx_count16 == 4'd0 && tx_bitcount == 4'd9
                   |=> uart_tx == 1'b1 && !tx_busy && tx_done);

  // tx_done pulse and causality
  assert property (tx_done |=> !tx_done);
  assert property (tx_done |-> $past(enable16 && tx_busy && tx_count16 == 4'd0 && tx_bitcount == 4'd9));

  // --------------------
  // Reset value checks
  // --------------------
  assert property (disable iff (1'b0)
                   sys_rst |-> (tx_done == 1'b0 && tx_busy == 1'b0 && uart_tx == 1'b1 &&
                                rx_done == 1'b0 && rx_busy == 1'b0 &&
                                rx_count16 == 4'd0 && rx_bitcount == 4'd0 &&
                                break == 1'b0 && uart_rx_r == 1'b0));

  // --------------------
  // Coverage
  // --------------------
  cover property (!sys_rst ##1 enable16);
  cover property (tx_wr ##[1:$] tx_done);
  cover property (enable16 && !rx_busy && (~uart_rx2 & uart_rx_r) ##[1:$] rx_done);
  cover property (enable16 && !rx_busy && (~uart_rx2 & uart_rx_r) ##[1:$] break);

endmodule

bind uart_transceiver uart_transceiver_sva U_UART_TRANSCEIVER_SVA();