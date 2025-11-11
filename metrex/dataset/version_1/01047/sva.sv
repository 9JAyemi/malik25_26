// SVA for echotest. Bind this file alongside the DUT.
// Focused, concise checks and covers across all compile-time options.

module echotest_sva
(
  input  logic        i_clk,
  input  logic        i_uart_rx,
  input  logic        o_uart_tx
`ifdef OPT_DUMBECHO
 ,input  logic        r_uart_tx
`else
 ,input  logic        pwr_reset
 ,input  logic [30:0] i_setup
 ,input  logic        rx_stb
 ,input  logic [7:0]  rx_data
 ,input  logic        rx_break
 ,input  logic        rx_perr
 ,input  logic        rx_ferr
 ,input  logic        rx_ignored
 ,input  logic        tx_busy
`endif
);

  default clocking cb @(posedge i_clk); endclocking

  logic f_past_valid;
  initial f_past_valid = 1'b0;
  always @(posedge i_clk) f_past_valid <= 1'b1;

  // Common: output is never X/Z after time 0
  assert property (f_past_valid |-> !$isunknown(o_uart_tx));

`ifdef OPT_DUMBECHO
  // Dumb echo: 1-cycle registered pass-through, init high
  assert property (!f_past_valid |-> o_uart_tx == 1'b1);
  assert property (f_past_valid |-> o_uart_tx == $past(i_uart_rx));
  // Continuous assign holds
  assert property (1'b1 |-> (o_uart_tx == r_uart_tx));

  // Coverage: input change propagates in 1 cycle
  cover property ($changed(i_uart_rx) ##1 (o_uart_tx == $past(i_uart_rx)));
  cover property ($fell(i_uart_rx) ##1 (o_uart_tx == 1'b0));
  cover property ($rose(i_uart_rx) ##1 (o_uart_tx == 1'b1));
`else
  // Reset behavior: one-cycle power-on reset pulse then low forever
  assert property (!f_past_valid |-> pwr_reset);
  assert property (f_past_valid |-> !pwr_reset);
  assert property (f_past_valid |-> $stable(pwr_reset));

`ifdef OPT_STANDALONE
  // Constant baud setup in standalone mode
  assert property (i_setup == 31'd868);
`endif

  // UART line idle high when not busy
  assert property (!tx_busy |-> o_uart_tx == 1'b1);

  // Received byte must be known on strobe
  assert property (rx_stb |-> !$isunknown(rx_data));

  // Interface signals should not be X after time 0
  assert property (f_past_valid |-> (!$isunknown(tx_busy) && !$isunknown(rx_stb)));

`ifdef USE_LITE_UART
  // Lite TX: write when not busy should make TX busy next cycle
  assert property (rx_stb && !tx_busy |-> ##1 tx_busy);
  // Coverage: RX write causes TX busy and then idle
  cover property (rx_stb && !tx_busy ##1 tx_busy ##[8:2048] !tx_busy);
`else
  // Full UART coverage: see a receive strobe and a TX busy window
  cover property (rx_stb ##[0:4096] tx_busy ##[64:32768] !tx_busy);

  // Error flag visibility coverage (if your environment ever drives them)
  cover property (rx_perr || rx_ferr || rx_break || rx_ignored);
`endif

  // End-to-end serial echo (start-bit to start-bit) coverage
  // A low transition on RX eventually produces a low on TX.
  cover property (f_past_valid && $fell(i_uart_rx) ##[1:200000] $fell(o_uart_tx));
`endif

endmodule

// Bind into the DUT
bind echotest echotest_sva i_echotest_sva (
  .i_clk(i_clk),
  .i_uart_rx(i_uart_rx),
  .o_uart_tx(o_uart_tx)
`ifdef OPT_DUMBECHO
 ,.r_uart_tx(r_uart_tx)
`else
 ,.pwr_reset(pwr_reset)
 ,.i_setup(i_setup)
 ,.rx_stb(rx_stb)
 ,.rx_data(rx_data)
 ,.rx_break(rx_break)
 ,.rx_perr(rx_perr)
 ,.rx_ferr(rx_ferr)
 ,.rx_ignored(rx_ignored)
 ,.tx_busy(tx_busy)
`endif
);