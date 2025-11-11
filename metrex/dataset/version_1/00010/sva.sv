// SVA for fifo_buffer
// Bind this file to the DUT. Focused, high-signal-coverage checks and key covers.

module fifo_buffer_sva #(parameter int DEPTH=64, WIDTH=8) (fifo_buffer dut);

  function automatic [6:0] inc_ptr(input [6:0] p);
    inc_ptr = (p == DEPTH-1) ? 7'd0 : p + 7'd1;
  endfunction

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (!dut.rst_n);

  // Basic reset/state ranges
  a_reset_vals:    assert property (!dut.rst_n |-> (dut.read_ptr==0 && dut.write_ptr==0 && dut.used_entries==0 && dut.rfifo_used==0 && dut.fifo_rdata==0));
  a_no_x:          assert property (!$isunknown({dut.fifo_EF, dut.rfifo_full, dut.fifo_rdata, dut.rfifo_used, dut.read_ptr, dut.write_ptr, dut.used_entries})));
  a_ranges:        assert property (dut.read_ptr < DEPTH && dut.write_ptr < DEPTH && dut.used_entries <= DEPTH && dut.rfifo_used <= DEPTH);

  // Flag correctness
  a_empty_flag:    assert property (dut.fifo_EF == (dut.used_entries == 0));
  a_full_flag:     assert property (dut.rfifo_full == (dut.used_entries == DEPTH));
  generate if (DEPTH > 0) begin : g_flags_mutex
    a_flags_mutex: assert property (!(dut.fifo_EF && dut.rfifo_full));
  end endgenerate

  // Write-side behavior (DUT writes whenever not full)
  a_no_write_on_full: assert property (dut.rfifo_full |=> (dut.write_ptr == $past(dut.write_ptr) && dut.used_entries == $past(dut.used_entries)));
  a_write_progress:   assert property (!dut.rfifo_full |=> (dut.write_ptr == inc_ptr($past(dut.write_ptr)) && dut.used_entries == $past(dut.used_entries)+1));

  // Read-side behavior
  a_no_read_when_empty: assert property ((dut.fifo_rd && dut.fifo_EF) |=> ($stable(dut.read_ptr) && $stable(dut.fifo_rdata) && $stable(dut.rfifo_used)));
  a_read_advances:      assert property ((dut.fifo_rd && !dut.fifo_EF) |=> (dut.read_ptr == inc_ptr($past(dut.read_ptr))));
  a_rfifo_used_update:  assert property ((dut.fifo_rd && !dut.fifo_EF) |=> (dut.rfifo_used == $past(dut.used_entries)-1));
  a_rfifo_used_hold:    assert property (((!dut.fifo_rd) || dut.fifo_EF) |=> (dut.rfifo_used == $past(dut.rfifo_used)));
  a_read_data_from_mem: assert property ((dut.fifo_rd && !dut.fifo_EF) |=> (dut.fifo_rdata == $past(dut.fifo_mem[dut.read_ptr])));

  // High-value semantic checks (catch design bugs)
  // Read must not increase occupancy
  a_read_never_increases_used: assert property ((dut.fifo_rd && !dut.fifo_EF) |=> (dut.used_entries <= $past(dut.used_entries)));
  // With the DUT's unconditional write when not full, a simultaneous read should keep occupancy constant
  a_rd_wr_same_cycle_keeps_used: assert property ((dut.fifo_rd && !dut.fifo_EF && !dut.rfifo_full) |=> (dut.used_entries == $past(dut.used_entries)));

  // Covers
  c_reach_full:          cover property (dut.rfifo_full);
  c_successful_read:     cover property (dut.fifo_rd && !dut.fifo_EF);
  c_wr_ptr_wrap:         cover property (($past(dut.write_ptr)==DEPTH-1) && (dut.write_ptr==0));
  c_rd_ptr_wrap:         cover property (($past(dut.read_ptr)==DEPTH-1) && (dut.read_ptr==0));
  c_empty_read_attempt:  cover property (dut.fifo_EF && dut.fifo_rd);

endmodule

// Bind into DUT
bind fifo_buffer fifo_buffer_sva #(.DEPTH(DEPTH), .WIDTH(WIDTH)) fifo_buffer_sva_i( .dut );