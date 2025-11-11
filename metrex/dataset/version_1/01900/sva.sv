// SVA for SPIinterface
// Bind this module to the DUT: bind SPIinterface SPIinterface_sva sva();

module SPIinterface_sva;

  // These names resolve in the scope of the bound SPIinterface instance
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // 0) Output mapping must match internals
  assert property (sclk     == sck_buffer);
  assert property (rxbuffer == rx_shift_register);
  assert property (done_out == done);

  // 1) Reset behavior (checks happen on cycle after rst=1)
  assert property (rst |=> tx_shift_register==16'd0 && tx_count==4'd0 && sdo==1'b1 && TxSTATE==TxType_idle);
  assert property (rst |=> rx_shift_register==8'h00 && rx_count==4'd0 && done==1'b0 && RxSTATE==RxType_idle);
  assert property (rst |=> clk_count==8'h00 && SCLKSTATE==SCLKType_idle && sck_previous==1'b1 && sck_buffer==1'b1);

  // 2) Start of transfer on transmit
  assert property ((TxSTATE==TxType_idle && transmit) |=> TxSTATE==TxType_transmitting);
  assert property ((RxSTATE==RxType_idle && transmit) |=> RxSTATE==RxType_recieving);
  assert property ((SCLKSTATE==SCLKType_idle && transmit) |=> SCLKSTATE==SCLKType_running);

  // 3) SCLK generation and divider protocol
  // SCLK must be stable high while idle (check from next cycle to avoid NBA timing)
  assert property ((SCLKSTATE==SCLKType_idle) |-> ##1 (sck_buffer==1'b1 && $stable(sck_buffer)));

  // Count/increment path in running state (non-divider cycles)
  assert property ((SCLKSTATE==SCLKType_running && clk_count!=CLKDIVIDER)
                   |=> clk_count==$past(clk_count)+1 && sck_previous==$past(sck_buffer));

  // First divider hit primes edge buffer, holds count and sck high
  assert property ((SCLKSTATE==SCLKType_running && clk_count==CLKDIVIDER && clk_edge_buffer==1'b0)
                   |=> clk_edge_buffer==1'b1 && sck_buffer==1'b1 && clk_count==CLKDIVIDER);

  // Second divider hit toggles sck and resets count
  assert property ((SCLKSTATE==SCLKType_running && clk_count==CLKDIVIDER && clk_edge_buffer==1'b1)
                   |=> clk_count==8'h00 && sck_buffer==$past(~sck_buffer));

  // Any sck toggle must be caused by divider while running after priming
  assert property ($changed(sck_buffer) |-> (SCLKSTATE==SCLKType_running &&
                                             $past(clk_count)==CLKDIVIDER &&
                                             clk_edge_buffer==1'b1));

  // 4) TX bit timing: shift on sclk falling edge while transmitting
  // Non-terminal bit
  assert property ((TxSTATE==TxType_transmitting && tx_count!=4'hF && sck_previous && !sck_buffer)
                   |=> tx_count==$past(tx_count)+1 &&
                       sdo==$past(tx_shift_register[15]) &&
                       tx_shift_register==={$past(tx_shift_register[14:0]),1'b0});

  // Terminal bit (bit 15)
  assert property ((TxSTATE==TxType_transmitting && tx_count==4'hF && sck_previous && !sck_buffer)
                   |=> TxSTATE==TxType_idle && tx_count==4'd0 &&
                       sdo==$past(tx_shift_register[15]));

  // While idle, tx_count must be 0
  assert property ((TxSTATE==TxType_idle) |-> tx_count==4'd0);

  // sdo only changes on a TX bit edge or gets forced high in idle when done
  assert property ($changed(sdo) |->
                   ($past(TxSTATE==TxType_transmitting) && $past(sck_previous && !sck_buffer)) ||
                   ($past(TxSTATE==TxType_idle) && $past(done)));

  // 5) RX bit timing: sample on sclk rising edge while receiving
  // Non-terminal bit
  assert property ((RxSTATE==RxType_recieving && rx_count!=4'hF && !sck_previous && sck_buffer)
                   |=> rx_count==$past(rx_count)+1 &&
                       rx_shift_register==={$past(rx_shift_register[6:0]), $past(sdi)});

  // Terminal bit (bit 15) sets done and returns to idle
  assert property ((RxSTATE==RxType_recieving && rx_count==4'hF && !sck_previous && sck_buffer)
                   |=> RxSTATE==RxType_idle && rx_count==4'd0 && done==1'b1 &&
                       rx_shift_register==={$past(rx_shift_register[6:0]), $past(sdi)});

  // While idle, rx_count must be 0
  assert property ((RxSTATE==RxType_idle) |-> rx_count==4'd0);

  // 6) done behavior: width and effect on SCLK
  // done stays high for exactly two cycles, then clears
  assert property ($rose(done) |-> done ##1 done ##1 !done);

  // After done rises, SCLKSTATE must go idle on the next cycle
  assert property ($rose(done) |=> SCLKSTATE==SCLKType_idle);

  // 7) Simple end-to-end coverages
  // Cover a complete 16-bit transfer (TX and RX edges observed) ending in done
  cover property (transmit && TxSTATE==TxType_idle && RxSTATE==RxType_idle && SCLKSTATE==SCLKType_idle
                  ##1 TxSTATE==TxType_transmitting && RxSTATE==RxType_recieving && SCLKSTATE==SCLKType_running
                  ##[1:$] (sck_previous && !sck_buffer) [*16]
                  ##[1:$] (!sck_previous && sck_buffer) [*16]
                  ##1 done);

  // Cover sclk toggling at least once in running state
  cover property (SCLKSTATE==SCLKType_running ##[1:$] $changed(sck_buffer));

  // Cover sdo returning high in idle after transfer complete
  cover property ($rose(done) ##2 (TxSTATE==TxType_idle && sdo==1'b1));

endmodule