// SVA for video_sys_jtag_uart_0_sim_scfifo_r
// Focused, high-quality checks and coverage

module video_sys_jtag_uart_0_sim_scfifo_r_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        fifo_rd,
  input  logic [5:0]  rfifo_used,
  input  logic        fifo_EF,
  input  logic        rfifo_full,
  input  logic [7:0]  fifo_rdata
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Basic invariants
  // Range and no-X on status
  ap_used_range:      assert property (rfifo_used <= 6'd64);
  ap_flags_known:     assert property (!$isunknown({fifo_EF, rfifo_full, rfifo_used}));

  // Flag correctness
  ap_empty_flag_ok:   assert property (fifo_EF == (rfifo_used == 6'd0));
  ap_full_flag_ok:    assert property (rfifo_full == (rfifo_used == 6'd64));

  // No underflow (read only when not empty)
  ap_no_underflow:    assert property (fifo_rd |-> !fifo_EF);

  // rfifo_used next-state behavior
  ap_used_dec_on_rd:  assert property ($past(rst_n) && $past(fifo_rd) && ($past(rfifo_used) > 0)
                                       |-> rfifo_used == $past(rfifo_used) - 1);
  ap_used_inc_on_idle:assert property ($past(rst_n) && !$past(fifo_rd) && ($past(rfifo_used) < 6'd64)
                                       |-> rfifo_used == $past(rfifo_used) + 1);
  ap_used_hold_on_full_no_rd:
                      assert property ($past(rst_n) && !$past(fifo_rd) && ($past(rfifo_used) == 6'd64)
                                       |-> rfifo_used == 6'd64);
  // Step size limited to {-1,0,+1}
  ap_used_step_bound: assert property ($past(rst_n)
                                       |-> ( rfifo_used == $past(rfifo_used)
                                          || rfifo_used == $past(rfifo_used)+1
                                          || ($past(rfifo_used)>0 && rfifo_used == $past(rfifo_used)-1)));

  // Data path visibility: output only updates on read; known after a read
  ap_rdata_stable_no_rd:
                      assert property ($past(rst_n) && !$past(fifo_rd) |-> $stable(fifo_rdata));
  ap_rdata_known_after_rd:
                      assert property ($past(fifo_rd) |-> !$isunknown(fifo_rdata));

  // Reset results (derivable from rfifo_used)
  ap_reset_effects:   assert property (!rst_n |-> (rfifo_used==6'd0 && fifo_EF && !rfifo_full));

  // Coverage
  cv_reset_release:       cover property ($rose(rst_n));
  cv_fill_cross_full:     cover property ((rfifo_used==6'd63 && !fifo_rd) ##1 rfifo_full);
  cv_full_then_read:      cover property (rfifo_full && fifo_rd);
  cv_last_read_to_empty:  cover property ((rfifo_used==6'd1 && fifo_rd) ##1 fifo_EF);
  cv_empty_to_nonempty:   cover property (fifo_EF && !fifo_rd ##1 !fifo_EF);
  cv_read_when_nonempty:  cover property (fifo_rd && !fifo_EF);

endmodule

bind video_sys_jtag_uart_0_sim_scfifo_r video_sys_jtag_uart_0_sim_scfifo_r_sva sva_inst (.*);