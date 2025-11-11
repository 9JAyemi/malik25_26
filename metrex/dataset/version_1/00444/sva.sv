// SVA for uart. Bind this file to the uart module.
// Focus: protocol, timing/state transitions, data movement, and flags.

`ifndef UART_SVA_SV
`define UART_SVA_SV

bind uart uart_sva u_uart_sva();

module uart_sva;

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst_i);

  // -------------
  // Basic sanity
  // -------------
  // Output combinational equivalence
  assert property (tx_busy_o == (tx_busy | tx_buf_full | wr_i));

  // Synchronizer: i_rxd is 1-cycle delayed version of rxd_i (outside reset)
  assert property (i_rxd == $past(rxd_i));

  // Counters never go negative and decrement by 1 when non-zero
  assert property (tx_count >= 0);
  assert property (rx_count >= 0);
  assert property (tx_count > 0 |=> tx_count == $past(tx_count) - 1);
  assert property (rx_count > 0 |=> rx_count == $past(rx_count) - 1);

  // ----------------
  // Reset semantics
  // ----------------
  // One cycle after reset deassert, key state is cleared/idle
  assert property ($fell(rst_i) |=> (tx_count==0 && tx_bits==0 && tx_busy==0 && txd_o==1 &&
                                     tx_shift_reg==8'h00 && tx_buf==8'h00 && tx_buf_full==0));
  assert property ($fell(rst_i) |=> (rx_bits==0 && rx_count==0 && rx_ready_o==0 &&
                                     rx_shift_reg==8'h00 && data_o==8'h00 && break_o==0 && i_rxd==1));

  // ----------------
  // Transmit path
  // ----------------
  // wr_i sets tx_buf_full next cycle
  assert property (wr_i |=> tx_buf_full);

  // Idle line high and not busy when truly idle
  assert property (tx_bits==0 && tx_count==0 && !tx_buf_full && !wr_i |-> (txd_o==1 && tx_busy_o==0));

  // Start transmission when buffer present at a bit boundary
  assert property (tx_bits==0 && tx_count==0 && tx_buf_full |=> (txd_o==0 && tx_bits==1 &&
                                                                 tx_count==FULL_BIT &&
                                                                 tx_shift_reg==$past(tx_buf) &&
                                                                 tx_buf_full==0 && tx_busy==1));

  // While sending any bit (non-idle), report busy
  assert property (tx_bits!=0 |-> tx_busy_o);

  // Data bit shifting (LSB first) for bits 1..8
  genvar b;
  generate
    for (b=1; b<=8; b++) begin : TX_SHIFT_CHECK
      assert property (tx_count==0 && tx_bits==b |=> (txd_o == $past(tx_shift_reg[0]) &&
                                                      tx_shift_reg[6:0] == $past(tx_shift_reg[7:1]) &&
                                                      tx_bits == b+1 &&
                                                      tx_count == FULL_BIT));
    end
  endgenerate

  // Stop bit and return to idle
  assert property (tx_count==0 && tx_bits==9 |=> (txd_o==1 && tx_bits==0 && tx_count==FULL_BIT));

  // Start edge must originate from a pending buffer at prior boundary
  assert property ($fell(txd_o) |-> $past(tx_bits==0 && tx_count==0 && tx_buf_full));

  // ----------------
  // Receive path
  // ----------------
  // Clear ready on read
  assert property (rd_i |=> !rx_ready_o);

  // Detect start (falling edge) from idle and arm half-bit validation
  assert property (rx_count==0 && rx_bits==0 && i_rxd==0 |=> (rx_bits==1 && rx_count==HALF_BIT && break_o==0));

  // Validate start at half-bit; either continue or abort on false start
  assert property (rx_count==0 && rx_bits==1 && i_rxd==0 |=> (rx_bits==2 && rx_count==FULL_BIT && rx_shift_reg==8'h00));
  assert property (rx_count==0 && rx_bits==1 && i_rxd==1 |=> (rx_bits==0));

  // Shift in data bits on FULL_BIT strobes (bits 2..9)
  generate
    for (b=2; b<=9; b++) begin : RX_SHIFT_CHECK
      assert property (rx_count==0 && rx_bits==b |=> (rx_shift_reg == { $past(i_rxd), $past(rx_shift_reg[7:1]) } &&
                                                      rx_bits == b+1 &&
                                                      rx_count == FULL_BIT));
    end
  endgenerate

  // Stop bit good: latch byte and raise ready
  assert property (rx_count==0 && rx_bits==10 && i_rxd==1 |=> (rx_bits==0 && rx_count==0 &&
                                                               rx_ready_o==1 && data_o==$past(rx_shift_reg)));

  // Stop bit bad: flag break/framing error
  assert property (rx_count==0 && rx_bits==10 && i_rxd==0 |=> (rx_bits==0 && rx_count==FULL_BIT && break_o==1));

  // Ready/break rise causes
  assert property ($rose(rx_ready_o) |-> $past(rx_count==0 && rx_bits==10 && i_rxd==1));
  assert property ($rose(break_o)    |-> $past(rx_count==0 && rx_bits==10 && i_rxd==0));

  // ---------------
  // Coverage
  // ---------------
  // Transmit: observe a start bit, a stop, and an example byte
  cover property ($fell(txd_o));                         // TX start
  cover property (tx_count==0 && tx_bits==9 ##1 tx_bits==0 && txd_o==1); // TX stop->idle
  cover property ($fell(txd_o) && $past(tx_buf)==8'hA5); // TX of 0xA5

  // Receive: successful frame, specific value, and break
  cover property ($rose(rx_ready_o));                    // Any RX complete
  cover property ($rose(rx_ready_o) && data_o==8'h5A);   // RX of 0x5A
  cover property ($rose(break_o));                       // Framing error/break

endmodule

`endif // UART_SVA_SV