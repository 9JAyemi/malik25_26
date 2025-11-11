// SVA for fifo
bind fifo fifo_sva #(.WIDTH(WIDTH)) fifo_sva_i();

module fifo_sva #(parameter WIDTH = 8) ();
  // Bound into fifo scope; direct access to clk, reset, ports, and internals
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Shorthands
  wire wr_ok = wr_en && !full;
  wire rd_ok = rd_en && !empty;

  // Invariants and flags
  a_cnt_range:      assert property (count <= 5'd16);
  a_flag_empty:     assert property (empty == (count == 5'd0));
  a_flag_full:      assert property (full  == (count == 5'd16));
  a_not_both:       assert property (!(full && empty));
  a_empty_ptrs:     assert property (empty |-> head == tail);

  // Pointer step/acceptance (single-step, gated)
  a_head_step:      assert property (head == $past(head) + ($past(wr_ok) ? 5'd1 : 5'd0));
  a_tail_step:      assert property (tail == $past(tail) + ($past(rd_ok) ? 5'd1 : 5'd0));

  // Occupancy evolution
  a_count_step:     assert property (count == $past(count)
                                     + ($past(wr_ok) ? 5'd1 : 5'd0)
                                     - ($past(rd_ok) ? 5'd1 : 5'd0));

  // Boundary behavior when both enables asserted
  a_full_both:      assert property ($past(full)  && $past(wr_en) && $past(rd_en)
                                     |-> head == $past(head) && tail == $past(tail)+5'd1);
  a_empty_both:     assert property ($past(empty) && $past(wr_en) && $past(rd_en)
                                     |-> tail == $past(tail) && head == $past(head)+5'd1);

  // Blocked ops hold state
  a_block_wr:       assert property ($past(full)  && $past(wr_en) |-> head == $past(head));
  a_block_rd:       assert property ($past(empty) && $past(rd_en) |-> tail == $past(tail) && $stable(dout));

  // Data integrity
  a_write_store:    assert property ($past(wr_ok) |-> buffer[$past(head)] == $past(din));
  a_read_dout:      assert property ($past(rd_ok) |-> dout == $past(buffer[$past(tail)]));
  a_dout_only_read: assert property (!$past(rd_ok) |-> $stable(dout));

  // No X on key status
  a_no_x_status:    assert property (!$isunknown({full, empty, count}));

  // Functional coverage
  c_fill_to_full:   cover property (empty ##1 wr_ok [*16] ##1 full);
  c_drain_to_empty: cover property (full  ##1 rd_ok [*16] ##1 empty);
  c_simul_rw_mid:   cover property (!full && !empty && wr_en && rd_en);
  c_head_wrap:      cover property ($past(head)==5'd31 && head==5'd0);
  c_tail_wrap:      cover property ($past(tail)==5'd31 && tail==5'd0);
endmodule