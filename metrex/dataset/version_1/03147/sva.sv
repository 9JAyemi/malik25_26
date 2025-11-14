// SVA for fifo_generator
// Bind this module to the DUT: bind fifo_generator fifo_generator_sva sva();

module fifo_generator_sva;

  // Use DUT scope via bind (no ports)
  // Default clock/reset
  default clocking cb @(posedge s_axi_aclk); endclocking
  default disable iff (Rst0);

  // Basic combinational relations
  ap_comb_rel: assert property (1'b1 |-> (Q == mem[rd_ptr] && out == empty && txfifo_empty == (empty && !wr_enable[0])));

  // Reset clears state
  ap_reset_clear: assert property ($rose(Rst0) |=> (count == 3'd0 && wr_ptr == 3'd0 && rd_ptr == 3'd0));

  // Empty reflects count==0
  ap_empty_eq_count0: assert property (empty == (count == 3'd0));

  // Enables are combinationally equivalent to inputs
  ap_wr_en_eq: assert property (wr_enable[0] == E);
  ap_rd_en_eq: assert property (rd_enable[0] == (fifo_tx_en && !empty));

  // No X on key state/outputs
  ap_no_x: assert property (!$isunknown({wr_ptr, rd_ptr, count, empty, out, txfifo_empty, wr_enable[0], rd_enable[0], Q})));

  // Count update semantics
  ap_cnt_hold_no_act: assert property (!$past(wr_enable[0] || rd_enable[0]) |=> count == $past(count));
  ap_cnt_inc_write:   assert property ($past(wr_enable[0] && !rd_enable[0]) |=> count == $past(count) + 3'd1);
  ap_cnt_dec_read:    assert property ($past(rd_enable[0] && !wr_enable[0]) |=> count == $past(count) - 3'd1);
  // Note: current RTL decrements when read and write occur together in same cycle
  ap_cnt_both_dec:    assert property ($past(wr_enable[0] && rd_enable[0]) |=> count == $past(count) - 3'd1);

  // Pointer updates and wrap
  ap_wr_ptr_upd: assert property ($past(E) |=> wr_ptr == (($past(wr_ptr) == 3'd7) ? 3'd0 : $past(wr_ptr) + 3'd1));
  ap_wr_ptr_hold: assert property (!$past(E) |=> wr_ptr == $past(wr_ptr));

  // BUG CHECK: next_rd_ptr lacks default assignment in RTL. rd_ptr should hold when no read.
  ap_rd_ptr_upd:  assert property ($past(fifo_tx_en && !$past(empty)) |=> rd_ptr == (($past(rd_ptr) == 3'd7) ? 3'd0 : $past(rd_ptr) + 3'd1));
  ap_rd_ptr_hold: assert property (!$past(fifo_tx_en && !$past(empty)) |=> rd_ptr == $past(rd_ptr));

  // No read when empty
  ap_no_read_on_empty: assert property (empty |-> !rd_enable[0]);

  // Optional overflow protection (environment/DUT must prevent write on full)
  ap_no_write_on_full: assert property (!(count == 3'd7 && E));

  // Write data integrity (DIA is dropped by RTL due to width; only D is stored)
  ap_write_data: assert property ($past(wr_enable[0]) |=> mem[$past(wr_ptr)] == $past(D));

  // Coverage

  // Empty -> write -> non-empty, then drain to empty with no concurrent write
  cv_empty_fill_drain: cover property ((count == 3'd0) ##1 E ##1 (count > 3'd0) ##[1:$] (!E && fifo_tx_en && count == 3'd1) ##1 (count == 3'd0));

  // Write pointer wrap 6->7->0
  cv_wrptr_wrap: cover property ((wr_ptr == 3'd6 && E) ##1 (wr_ptr == 3'd7 && E) ##1 (wr_ptr == 3'd0));

  // Read pointer wrap 6->7->0
  cv_rdptr_wrap: cover property ((rd_ptr == 3'd6 && fifo_tx_en && !empty) ##1 (rd_ptr == 3'd7 && fifo_tx_en && !empty) ##1 (rd_ptr == 3'd0));

  // Simultaneous read and write when not empty
  cv_rd_wr_same_cycle: cover property (E && fifo_tx_en && !empty);

  // txfifo_empty toggle 1->0->1
  cv_txfifo_empty_toggle: cover property (txfifo_empty ##[1:$] !txfifo_empty ##[1:$] txfifo_empty);

endmodule