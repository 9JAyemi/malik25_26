// SVA for module fpga
module fpga_sva;

  default clocking cb @(posedge clk_125mhz); endclocking

  // No X/Z on key signals
  assert property (!$isunknown({rst_125mhz, btnu, btnl, btnd, btnr, btnc,
                                ledu, ledl, ledd, ledr, ledc, led,
                                uart_rxd, uart_txd, uart_rts, uart_cts,
                                led_state, uart_data}));

  // Reset behavior
  assert property (rst_125mhz |-> (led_state==5'b0 && uart_data==8'h00
                                   && {ledu,ledl,ledd,ledr,ledc}==5'b0
                                   && led==8'h00 && uart_rxd==1'b0 && uart_cts==1'b0));

  // LED state/register update is 1-cycle image of buttons
  assert property (!$past(rst_125mhz) |-> led_state == $past({btnc,btnr,btnd,btnl,btnu}));

  // LED outputs match register and are 1-cycle image of buttons
  assert property ({ledc, ledr, ledd, ledl, ledu} == led_state);
  assert property (!$past(rst_125mhz) |-> {ledc, ledr, ledd, ledl, ledu} == $past({btnc,btnr,btnd,btnl,btnu}));

  // LED bus constant
  assert property (led == 8'h00);

  // UART output ties
  assert property (uart_rxd == uart_data[0] && uart_cts == uart_data[1]);

  // UART upper bits stuck at zero; CTS always zero
  assert property (uart_data[7:2] == 6'b0);
  assert property (uart_cts == 1'b0);

  // UART state update/hold behavior (1-cycle latency)
  assert property (!$past(rst_125mhz) &&  $past(uart_rxd) |-> uart_data == {7'b0, $past(uart_txd)});
  assert property (!$past(rst_125mhz) && !$past(uart_rxd) |-> uart_data == $past(uart_data));

  // Covers
  cover property (rst_125mhz ##1 !rst_125mhz);
  cover property (!$past(rst_125mhz) && $changed({btnu,btnl,btnd,btnr,btnc}));
  cover property (!$past(rst_125mhz) && $past(uart_rxd) && !$past(uart_txd) ##1 uart_data==8'h00);
  cover property (!$past(rst_125mhz) && $past(uart_rxd) &&  $past(uart_txd) ##1 uart_data==8'h01);

endmodule

bind fpga fpga_sva fpga_sva_i();