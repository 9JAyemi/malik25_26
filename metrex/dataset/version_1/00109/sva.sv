// SVA for SPI_sender — concise, high-quality checks and coverage
// Bind into the DUT so we can see internal regs
bind SPI_sender SPI_sender_sva spi_sender_sva();

module SPI_sender_sva;

  // Use DUT’s clock/reset
  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  // Reset values (only what DUT actually resets)
  assert property (@cb RST |-> (counter==0 && shift_register==0 && data_out==0 &&
                                bit_counter==0 && ss_done==0 && DONE==0));

  // When ST is low, all state holds
  assert property (@cb !ST |=> $stable({counter,shift_register,data_out,bit_counter,ss_done,DONE,SS}));

  // Counter behavior
  assert property (@cb counter <= T_DIV);
  assert property (@cb ST && (counter <  T_DIV) |=> counter == $past(counter)+1);
  assert property (@cb ST && (counter >= T_DIV) |=> counter == 0);

  // SCK definition
  assert property (@cb SCK == (counter < (T_DIV/2)));

  // ss_done behavior
  assert property (@cb $rose(ss_done) |-> SS==0);         // SS must go low when ss_done rises
  assert property (@cb ss_done |=> ss_done);               // sticky until reset

  // SS behavior during active transfer (before DONE)
  assert property (@cb ss_done && !DONE |-> SS==0);

  // DONE behavior
  assert property (@cb DONE |-> SS==1);                    // DONE implies SS high same cycle
  assert property (@cb DONE |=> DONE);                     // DONE sticky until reset

  // bit_counter range and updates
  assert property (@cb bit_counter <= 7);
  assert property (@cb ST && ss_done && (counter==T_DIV) && (bit_counter<7)
                        |=> bit_counter == $past(bit_counter)+1);
  assert property (@cb ST && ss_done && (counter==T_DIV) && (bit_counter>=7)
                        |=> bit_counter == 0);

  // shift_register updates only on shift cycles; and shifts correctly
  assert property (@cb ST && ss_done && (counter==T_DIV) && (bit_counter<7)
                        |=> shift_register[6:0] == $past(shift_register[7:1]));
  // MSB gets DATA[bit_counter] when shifting
  assert property (@cb ST && ss_done && (counter==T_DIV) && (bit_counter<7)
                        |=> shift_register[7] == $past(DATA[$past(bit_counter)]));

  // No shift_register change when not a shift cycle (including final byte cycle)
  assert property (@cb !(ST && ss_done && (counter==T_DIV) && (bit_counter<7))
                        |=> $stable(shift_register));

  // data_out captures shift_register on final wrap
  assert property (@cb ST && ss_done && (counter==T_DIV) && (bit_counter>=7)
                        |=> data_out == $past(shift_register));

  // MOSI mapping to shift_register
  assert property (@cb MOSI == shift_register[7-bit_counter]);

  // Coverage: observe a complete transaction (ss asserted low, 8 shifts, then DONE)
  cover property (@cb $rose(ss_done)
                  ##[1:$] (ss_done && (bit_counter==7) && (counter==T_Div))
                  ##1 $rose(DONE));

  // Coverage: degenerate divider case (T_DIV==0)
  cover property (@cb ST && (T_DIV==0)
                  ##1 $rose(ss_done)
                  ##[1:8] $rose(DONE));

endmodule