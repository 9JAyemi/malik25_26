// SVA for LCD_driver
// Bind this file to the DUT
module LCD_driver_sva (LCD_driver dut);

  default clocking cb @ (posedge dut.clk); endclocking
  default disable iff ($initstate);

  // Basic tie-offs and legality
  assert property (dut.addr == 16'h0000);
  assert property (dut.busy === dut.busy_reg);
  assert property (dut.state inside {dut.IDLE, dut.WRITE_CMD, dut.WRITE_DATA, dut.CLEAR_SCREEN});

  // Launch from IDLE
  assert property ((dut.state==dut.IDLE && dut.ctrl==4'b0001)
                   |=> (dut.lcd_ctrl==4'b0000 && dut.lcd_data==8'h01 &&
                        dut.state==dut.WRITE_CMD && dut.counter==4'd0 && dut.busy==1));
  assert property ((dut.state==dut.IDLE && dut.ctrl==4'b0010)
                   |=> (dut.lcd_ctrl==4'b0000 && dut.lcd_data==$past(dut.data[7:0]) &&
                        dut.state==dut.WRITE_DATA && dut.counter==4'd0 && dut.busy==1));
  assert property ((dut.state==dut.IDLE && dut.ctrl==4'b0011)
                   |=> (dut.lcd_ctrl==4'b0000 && dut.lcd_data==8'h01 &&
                        dut.state==dut.CLEAR_SCREEN && dut.counter==4'd0 && dut.busy==1));
  assert property ((dut.state==dut.IDLE && !(dut.ctrl inside {4'b0001,4'b0010,4'b0011}))
                   |=> (dut.state==dut.IDLE && dut.busy==0));

  // Progress while busy (counter increments, stay in state, lcd_ctrl low)
  assert property ((dut.state==dut.WRITE_CMD  && dut.counter < dut.LCD_BUSY_TIME-1)
                   |=> (dut.state==dut.WRITE_CMD  && dut.counter==$past(dut.counter)+1 && dut.busy==1 && dut.lcd_ctrl==4'b0000));
  assert property ((dut.state==dut.WRITE_DATA && dut.counter < dut.LCD_BUSY_TIME-1)
                   |=> (dut.state==dut.WRITE_DATA && dut.counter==$past(dut.counter)+1 && dut.busy==1 && dut.lcd_ctrl==4'b0000));
  assert property ((dut.state==dut.CLEAR_SCREEN && dut.counter < dut.LCD_BUSY_TIME-1)
                   |=> (dut.state==dut.CLEAR_SCREEN && dut.counter==$past(dut.counter)+1 && dut.busy==1 && dut.lcd_ctrl==4'b0000));

  // Completion on last count (counter observed max is LCD_BUSY_TIME-1)
  assert property ((dut.state==dut.WRITE_CMD  && dut.counter==dut.LCD_BUSY_TIME-1)
                   |=> (dut.state==dut.IDLE && dut.counter==0 && dut.busy==0 && dut.lcd_ctrl==4'b0001));
  assert property ((dut.state==dut.WRITE_DATA && dut.counter==dut.LCD_BUSY_TIME-1)
                   |=> (dut.state==dut.IDLE && dut.counter==0 && dut.busy==0 && dut.lcd_ctrl==4'b0001 &&
                        dut.lcd_data==$past(dut.data[15:8])));
  assert property ((dut.state==dut.CLEAR_SCREEN && dut.counter==dut.LCD_BUSY_TIME-1)
                   |=> (dut.state==dut.IDLE && dut.counter==0 && dut.busy==0 && dut.lcd_ctrl==4'b0001));

  // In any non-IDLE cycle, busy must be 1, lcd_ctrl low, and counter in range
  assert property ((dut.state!=dut.IDLE) |-> (dut.busy==1 && dut.lcd_ctrl==4'b0000 && dut.counter < dut.LCD_BUSY_TIME));

  // Coverage
  cover property ((dut.state==dut.IDLE && dut.ctrl==4'b0001)
                  ##1 (dut.state==dut.WRITE_CMD && dut.busy)[*dut.LCD_BUSY_TIME]
                  ##1 (dut.state==dut.IDLE && dut.busy==0 && dut.lcd_ctrl==4'b0001));
  cover property ((dut.state==dut.IDLE && dut.ctrl==4'b0010)
                  ##1 (dut.state==dut.WRITE_DATA && dut.busy)[*dut.LCD_BUSY_TIME]
                  ##1 (dut.state==dut.IDLE && dut.busy==0 && dut.lcd_ctrl==4'b0001));
  cover property ((dut.state==dut.IDLE && dut.ctrl==4'b0011)
                  ##1 (dut.state==dut.CLEAR_SCREEN && dut.busy)[*dut.LCD_BUSY_TIME]
                  ##1 (dut.state==dut.IDLE && dut.busy==0 && dut.lcd_ctrl==4'b0001));
  cover property (dut.state==dut.IDLE && !(dut.ctrl inside {4'b0001,4'b0010,4'b0011}));
  // Back-to-back command coverage
  cover property ((dut.state==dut.IDLE && dut.ctrl==4'b0010)
                  ##1 (dut.state==dut.WRITE_DATA)[*dut.LCD_BUSY_TIME]
                  ##1 (dut.state==dut.IDLE)
                  ##1 (dut.ctrl==4'b0001)
                  ##1 (dut.state==dut.WRITE_CMD));

endmodule

bind LCD_driver LCD_driver_sva sva_i();