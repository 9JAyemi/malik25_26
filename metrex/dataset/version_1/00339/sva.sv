// SVA for lcd_controller
// Bind into the DUT instance
bind lcd_controller lcd_controller_sva sva_i();

module lcd_controller_sva;

  // Use DUT scope names directly
  // Clocking and reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helpers
  function automatic [7:0] cmd_map(input [7:0] d);
    cmd_map = (d[7:4] == 4'h0) ? d : 8'h00;
  endfunction

  // Outputs follow their internal regs (1-stage), and pipeline from inputs (2-stage)
  assert property (o_write_n          == $past(write_n));
  assert property (o_read_n           == $past(read_n));
  assert property (o_cmd_finished     == $past(cmd_finished));
  assert property (o_cs_n             == $past(cs_n));
  assert property (o_reset_n          == $past(reset_n));
  assert property (o_data_out_en      == $past(data_out_en));
  assert property (o_register_data_sel== $past(register_data_sel));

  assert property (write_n            == $past(~i_cmd_write_stb));
  assert property (read_n             == $past(~i_cmd_read_stb));
  assert property (o_write_n          == $past(~i_cmd_write_stb,2));
  assert property (o_read_n           == $past(~i_cmd_read_stb,2));
  assert property (register_data_sel  == $past(i_cmd_mode));
  assert property (o_register_data_sel== $past(i_cmd_mode,2));

  // Static control lines driven high every cycle (observable after pipeline)
  assert property (cs_n == 1'b1);
  assert property (reset_n == 1'b1);
  assert property (data_out_en == 1'b1);
  assert property (o_cs_n == 1'b1);
  assert property (o_reset_n == 1'b1);
  assert property (o_data_out_en == 1'b1);

  // Command-mode behavior
  // Write: capture command byte
  assert property (i_enable && i_cmd_mode && i_cmd_write_stb |=> cmd_reg == $past(i_cmd_data));
  // Read: return mapped data on next cycle
  assert property (i_enable && i_cmd_mode && i_cmd_read_stb  |=> o_cmd_data == cmd_map($past(i_cmd_data)));
  // cmd_finished sets on any cmd strobe and sticks until reset
  assert property (i_enable && i_cmd_mode && (i_cmd_write_stb || i_cmd_read_stb) |=> cmd_finished);
  assert property ($rose(cmd_finished) |-> cmd_finished throughout (!rst));
  assert property ($rose(o_cmd_finished) |-> o_cmd_finished throughout (!rst));
  // Priority: write over read when both high
  assert property (i_enable && i_cmd_mode && i_cmd_write_stb && i_cmd_read_stb |=> cmd_reg == $past(i_cmd_data) and $stable(o_cmd_data));

  // Data-mode behavior (as coded)
  // When write_n is 1, capture i_data into data_reg
  assert property (i_enable && !i_cmd_mode && write_n |=> data_reg == $past(i_data));
  // When read_n is 1, drive o_data with current data_reg
  assert property (i_enable && !i_cmd_mode && read_n  |=> o_data   == $past(data_reg));
  // If both write_n and read_n are 1, write path has priority (read path does not update o_data)
  assert property (i_enable && !i_cmd_mode && write_n && read_n |=> data_reg == $past(i_data) and $stable(o_data));
  // In command mode, data path remains idle
  assert property (i_cmd_mode |=> $stable(data_reg) and $stable(o_data));

  // Reset effects on stateful regs (synchronous)
  // Checked on first cycle out of reset deassertion
  assert property ($fell(rst) |=> cmd_reg == 8'h00 && data_reg == 8'h00 && cmd_finished == 1'b0);

  // Coverage
  cover property ($rose(rst));
  cover property (i_enable && i_cmd_mode && i_cmd_write_stb);
  cover property (i_enable && i_cmd_mode && i_cmd_read_stb && (i_cmd_data[7:4] == 4'h0));
  cover property (i_enable && i_cmd_mode && i_cmd_read_stb && (i_cmd_data[7:4] != 4'h0));
  cover property (i_enable && !i_cmd_mode && write_n);
  cover property (i_enable && !i_cmd_mode && read_n);
  cover property (i_enable && i_cmd_mode && i_cmd_write_stb && i_cmd_read_stb);

endmodule