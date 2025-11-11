// SVA for tracking_camera_system_jtag_uart_0_sim_scfifo_r
// Bind this checker to the DUT. Uses internal regs via bind scope.

module tracking_camera_system_jtag_uart_0_sim_scfifo_r_sva;

  // Default clock/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity: outputs never X/Z when out of reset
  a_known_outputs: assert property (!$isunknown({fifo_EF, rfifo_full, fifo_rdata, rfifo_used, rfifo_entries})));

  // Async reset behavior for fifo_rd_d
  a_rst_fifo_rd_d: assert property (@(posedge clk or negedge rst_n) !rst_n |-> (fifo_rd_d == 1'b0));

  // fifo_rd_d is a 1-cycle pipe of fifo_rd
  a_pipe_rd: assert property (fifo_rd_d == $past(fifo_rd));

  // bytes_left update semantics
  a_bytes_dec:    assert property (fifo_rd_d && !$isunknown($past(bytes_left)) |=> bytes_left == $past(bytes_left) - 32'd1);
  a_bytes_stable: assert property (!fifo_rd_d && !$isunknown($past(bytes_left)) |=> bytes_left == $past(bytes_left));

  // No underflow read allowed (design assumption)
  a_no_underflow: assert property (!(bytes_left == 32'd0 && fifo_rd_d));

  // Combinational outputs equivalence
  a_fifo_EF_eq:     assert property (fifo_EF == (bytes_left == 32'd0));
  a_full_eq:        assert property (rfifo_full == (bytes_left > 32'd64));
  a_entries_eq:     assert property (rfifo_entries == {1'b0, bytes_left[5:0]});
  a_entries_msb0:   assert property (rfifo_entries[6] == 1'b0);
  a_rdata_zero:     assert property (fifo_rdata == 8'h00);

  // rfifo_used matches truncation of 64 - rfifo_entries as in RTL
  a_used_calc:      assert property (rfifo_used == ( (32'd64 - {25'd0, rfifo_entries})[5:0] ));

  // Simple implications derived from definitions
  a_EF_implies_not_full: assert property (fifo_EF |-> !rfifo_full);
  a_EF_implies_entries0: assert property (fifo_EF |-> rfifo_entries == 7'd0);

  // Coverage
  c_rd_happens:       cover property (fifo_rd_d);
  c_hit_empty:        cover property (fifo_EF);
  c_hit_full_range:   cover property (rfifo_full);
  c_dec_transition:   cover property (fifo_rd_d && !$isunknown($past(bytes_left)) ##1 bytes_left == $past(bytes_left) - 32'd1);
  c_entries_extremes: cover property (rfifo_entries == 7'd0 or rfifo_entries == 7'd63);

endmodule

bind tracking_camera_system_jtag_uart_0_sim_scfifo_r tracking_camera_system_jtag_uart_0_sim_scfifo_r_sva sva_inst();