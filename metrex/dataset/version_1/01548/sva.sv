// SVA for module main
// Bind-in assertion module; references DUT signals directly
module main_sva ();
  default clocking cb @ (posedge CLK22M5792); endclocking

  // Counter increments by +4 each cycle (mod 2^32), gated for X
  a_inc4: assert property( !$isunknown({counter_ff,$past(counter_ff)})
                           |-> counter_ff == $past(counter_ff) + 32'd4 );

  // Output mappings to counter bits
  a_led_m:   assert property( !$isunknown(counter_ff[28])     |-> LED_M == counter_ff[28] );
  a_led_bus: assert property( !$isunknown(counter_ff[27:24])  |-> LED   == counter_ff[27:24] );

  a_uart:    assert property( !$isunknown(counter_ff[15:14])  |-> {UART_RXD,UART_TXD} == counter_ff[15:14] );

  a_nib19_16_spdif: assert property( !$isunknown(counter_ff[19:16]) |-> SPDIF == counter_ff[19:16] );
  a_nib19_16_gpio:  assert property( !$isunknown(counter_ff[19:16]) |-> GPIO  == counter_ff[19:16] );
  a_nib19_16_spi:   assert property( !$isunknown(counter_ff[19:16]) |-> {SPI_SCK,SPI_SSEL,SPI_MOSI,SPI_MISO} == counter_ff[19:16] );
  a_nib19_16_i2s0:  assert property( !$isunknown(counter_ff[19:16]) |-> {I2S0_SCK,I2S0_SDA,I2S0_WS,I2S0_MCLK} == counter_ff[19:16] );
  a_nib19_16_i2s1:  assert property( !$isunknown(counter_ff[19:16]) |-> {I2S1_SCK,I2S1_SDA,I2S1_WS,I2S1_MCLK_P} == counter_ff[19:16] );
  a_i2s1_mclkn:     assert property( !$isunknown(counter_ff[15])    |-> I2S1_MCLK_N == counter_ff[15] );
  a_nib19_16_i2s2:  assert property( !$isunknown(counter_ff[19:16]) |-> {I2S2_SCK,I2S2_SDA,I2S2_WS,I2S2_MCLK} == counter_ff[19:16] );
  a_nib19_16_sata:  assert property( !$isunknown(counter_ff[19:16]) |-> {SATA_TX_P,SATA_TX_N,SATA_RX_P,SATA_RX_N} == counter_ff[19:16] );

  // Cross-consistency among duplicated wirings
  a_eq_gpio:  assert property( SPDIF == GPIO );
  a_eq_spi:   assert property( SPDIF == {SPI_SCK,SPI_SSEL,SPI_MOSI,SPI_MISO} );
  a_eq_i2s0:  assert property( SPDIF == {I2S0_SCK,I2S0_SDA,I2S0_WS,I2S0_MCLK} );
  a_eq_i2s1:  assert property( SPDIF == {I2S1_SCK,I2S1_SDA,I2S1_WS,I2S1_MCLK_P} );
  a_eq_i2s2:  assert property( SPDIF == {I2S2_SCK,I2S2_SDA,I2S2_WS,I2S2_MCLK} );
  a_eq_sata:  assert property( SPDIF == {SATA_TX_P,SATA_TX_N,SATA_RX_P,SATA_RX_N} );
  a_eq_mclkn_uart: assert property( I2S1_MCLK_N == UART_RXD );

  // Functional coverage: each unique driven counter bit toggles
  c_led_m_tgl:   cover property( !$isunknown(LED_M)    && (LED_M    ^ $past(LED_M)) );
  c_led0_tgl:    cover property( !$isunknown(LED[0])   && (LED[0]   ^ $past(LED[0])) );
  c_led1_tgl:    cover property( !$isunknown(LED[1])   && (LED[1]   ^ $past(LED[1])) );
  c_led2_tgl:    cover property( !$isunknown(LED[2])   && (LED[2]   ^ $past(LED[2])) );
  c_led3_tgl:    cover property( !$isunknown(LED[3])   && (LED[3]   ^ $past(LED[3])) );

  c_uart_txd_tgl: cover property( !$isunknown(UART_TXD) && (UART_TXD ^ $past(UART_TXD)) );
  c_uart_rxd_tgl: cover property( !$isunknown(UART_RXD) && (UART_RXD ^ $past(UART_RXD)) );

  c_spdif0_tgl:  cover property( !$isunknown(SPDIF[0]) && (SPDIF[0] ^ $past(SPDIF[0])) );
  c_spdif1_tgl:  cover property( !$isunknown(SPDIF[1]) && (SPDIF[1] ^ $past(SPDIF[1])) );
  c_spdif2_tgl:  cover property( !$isunknown(SPDIF[2]) && (SPDIF[2] ^ $past(SPDIF[2])) );
  c_spdif3_tgl:  cover property( !$isunknown(SPDIF[3]) && (SPDIF[3] ^ $past(SPDIF[3])) );

  // Counter activity seen
  c_counter_moves: cover property( !$isunknown({counter_ff,$past(counter_ff)}) && counter_ff != $past(counter_ff) );
endmodule

bind main main_sva main_sva_i();