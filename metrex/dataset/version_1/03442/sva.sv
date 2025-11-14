// SystemVerilog Assertions for VerilogModule
// Bind-in module; references DUT internals directly.
module VerilogModule_sva;

  // d0/d1/d2/d3 load on KEY[2] edge with proper select; others stable
  property p_load_d0;
    @(posedge KEY[2]) (SW[17:16]==2'd0)
      |=> (d0 == $past(SW[15:0])) && $stable(d1) && $stable(d2) && $stable(d3);
  endproperty
  assert property (p_load_d0);

  property p_load_d1;
    @(posedge KEY[2]) (SW[17:16]==2'd1)
      |=> (d1 == $past(SW[15:0])) && $stable(d0) && $stable(d2) && $stable(d3);
  endproperty
  assert property (p_load_d1);

  property p_load_d2;
    @(posedge KEY[2]) (SW[17:16]==2'd2)
      |=> (d2 == $past(SW[15:0])) && $stable(d0) && $stable(d1) && $stable(d3);
  endproperty
  assert property (p_load_d2);

  property p_load_d3;
    @(posedge KEY[2]) (SW[17:16]==2'd3)
      |=> (d3 == $past(SW[15:0])) && $stable(d0) && $stable(d1) && $stable(d2);
  endproperty
  assert property (p_load_d3);

  // d4 accumulator behavior on CLOCK_27 with KEY[0] as active-low reset
  assert property (@(posedge CLOCK_27)
    1 |=> d4 == ($past(KEY[0]) ? ($past(d4) + $past(d0)) : 16'd0));

  // LEDR captures d0 with zero-extension on CLOCK_27
  assert property (@(posedge CLOCK_27)
    1 |=> (LEDR[15:0] == $past(d0)) && (LEDR[17:16] == 2'b00));

  // LEDG forced to all ones on CLOCK_27
  assert property (@(posedge CLOCK_27)
    1 |=> (LEDG == 9'h1FF));

  // 7-seg outputs: truncation of 16b to 7b and constants
  assert property (@(posedge CLOCK_27) HEX0 == d0[6:0]);
  assert property (@(posedge CLOCK_27) HEX1 == d1[6:0]);
  assert property (@(posedge CLOCK_27) HEX2 == d2[6:0]);
  assert property (@(posedge CLOCK_27) HEX3 == d3[6:0]);
  assert property (@(posedge CLOCK_27) HEX4 == d4[6:0]);
  assert property (@(posedge CLOCK_27) HEX5 == 7'b1111111);
  assert property (@(posedge CLOCK_27) HEX6 == 7'b1111111);
  assert property (@(posedge CLOCK_27) HEX7 == 7'b1111111);

  // UART_TXD is 1b truncation of {d0,d1,d2,d3,d4} -> LSB of d4
  assert property (@(posedge CLOCK_27) UART_TXD == d4[0]);

  // LCD control pins are constants
  assert property (@(posedge CLOCK_27) LCD_ON && LCD_BLON && LCD_EN && LCD_RS && !LCD_RW);

  // No X/Z on key observable outputs (sampled on CLOCK_27)
  assert property (@(posedge CLOCK_27)
    !$isunknown({HEX0,HEX1,HEX2,HEX3,HEX4,HEX5,HEX6,HEX7,LEDR,LEDG,UART_TXD,LCD_ON,LCD_BLON,LCD_RW,LCD_EN,LCD_RS}));

  // Coverage: exercise each DPDT selection and d4 behaviors
  cover property (@(posedge KEY[2]) (SW[17:16]==2'd0) ##1 (d0 == $past(SW[15:0])));
  cover property (@(posedge KEY[2]) (SW[17:16]==2'd1) ##1 (d1 == $past(SW[15:0])));
  cover property (@(posedge KEY[2]) (SW[17:16]==2'd2) ##1 (d2 == $past(SW[15:0])));
  cover property (@(posedge KEY[2]) (SW[17:16]==2'd3) ##1 (d3 == $past(SW[15:0])));

  cover property (@(posedge CLOCK_27) !$past(KEY[0]) ##1 (d4==16'd0)); // reset path
  cover property (@(posedge CLOCK_27) $past(KEY[0]) && (d4 == $past(d4)+$past(d0))); // add path
  cover property (@(posedge CLOCK_27) $past(KEY[0]) &&
                               (($past(d4)+$past(d0)) < $past(d4))); // d4 overflow

endmodule

bind VerilogModule VerilogModule_sva;