// SVA for nios_system_alu_control
// Bind into the DUT for checking and coverage

module nios_system_alu_control_sva (nios_system_alu_control dut);

  default clocking @(posedge dut.clk); endclocking
  default disable iff (!dut.reset_n)

  // Basic combinational relations
  a_out_port_matches_reg: assert property (dut.out_port == dut.data_out);
  a_read_upper_zero:      assert property (dut.readdata[31:3] == '0);
  a_read_mux_logic:       assert property (dut.readdata[2:0] ==
                                           ((dut.address==2'd0) ? dut.data_out : 3'd0));

  // Register behavior
  a_write_updates_reg: assert property (
    dut.chipselect && !dut.write_n && (dut.address==2'd0)
    |=> dut.data_out == $past(dut.writedata[2:0])
  );

  a_hold_without_write: assert property (
    !(dut.chipselect && !dut.write_n && (dut.address==2'd0))
    |=> dut.data_out == $past(dut.data_out)
  );

  // Asynchronous reset checks (outside disable)
  a_async_reset_clears: assert property (@(negedge dut.reset_n) ##0 (dut.data_out == 3'd0));
  a_reset_low_clears_ff: assert property (@(posedge dut.clk) !dut.reset_n |-> (dut.data_out == 3'd0));

  // Coverage
  c_write_addr0:        cover property (dut.chipselect && !dut.write_n && (dut.address==2'd0));
  c_write_min:          cover property (dut.chipselect && !dut.write_n && (dut.address==2'd0) &&
                                        dut.writedata[2:0]==3'd0);
  c_write_max:          cover property (dut.chipselect && !dut.write_n && (dut.address==2'd0) &&
                                        dut.writedata[2:0]==3'd7);
  c_read_hit:           cover property ((dut.address==2'd0) && (dut.readdata[2:0]==dut.data_out));
  c_read_miss_zero:     cover property ((dut.address!=2'd0) && (dut.readdata==32'd0));
  c_reset_write_read:   cover property (
                          !dut.reset_n ##1 dut.reset_n
                          ##[1:$] (dut.chipselect && !dut.write_n && (dut.address==2'd0))
                          ##1 ((dut.address==2'd0) && (dut.readdata[2:0]==dut.data_out))
                        );

endmodule

// Bind statement (place in a testbench or a package included in simulation)
bind nios_system_alu_control nios_system_alu_control_sva sva_inst(.dut);