// SVA for small_fifo
// Bind into DUT to check key behaviors, pointers, flags, data-path, and provide concise coverage.

checker small_fifo_sva;

  // Ring distance (write_ptr ahead of read_ptr)
  function automatic int unsigned dist (input int unsigned wp, rp);
    if (wp >= rp) dist = wp - rp; else dist = DEPTH - (rp - wp);
  endfunction

  // Pointer ranges
  a_wptr_range: assert property (@(posedge inclock) write_ptr < DEPTH);
  a_rptr_range: assert property (@(posedge outclock) read_ptr < DEPTH);

  // Write-side pointer behavior
  a_wptr_hold_no_write: assert property (@(posedge inclock)
    (!wren || full) |=> write_ptr == $past(write_ptr));
  a_wptr_inc_on_write: assert property (@(posedge inclock)
    (wren && !full) |=> write_ptr == (($past(write_ptr)==DEPTH-1) ? 0 : $past(write_ptr)+1));

  // Memory write data
  a_mem_write: assert property (@(posedge inclock)
    (wren && !full) |=> mem[$past(write_ptr)] == $past(data));

  // Read-side pointer behavior
  a_rptr_hold_no_read: assert property (@(posedge outclock)
    (!outclocken || empty) |=> read_ptr == $past(read_ptr));
  a_rptr_inc_on_read: assert property (@(posedge outclock)
    (outclocken && !empty) |=> read_ptr == (($past(read_ptr)==DEPTH-1) ? 0 : $past(read_ptr)+1));

  // q updates only on legal read, and returns memory data at sampled read_ptr
  a_q_change_only_on_read: assert property (@(posedge outclock)
    (q != $past(q)) |-> (outclocken && !empty));
  a_q_from_mem: assert property (@(posedge outclock)
    (outclocken && !empty) |=> q == $past(mem[read_ptr]));

  // Flag correctness on inclock edge (where flags are registered)
  a_empty_def: assert property (@(posedge inclock)
    empty == (read_ptr == write_ptr));

  // Full should reflect ring semantics (one slot empty)
  a_full_def_ring: assert property (@(posedge inclock)
    full == (write_ptr == ((read_ptr==0) ? DEPTH-1 : read_ptr-1)));

  // Flags mutual exclusion
  a_flags_mutex: assert property (@(posedge inclock) !(full && empty));

  // No pointer advance when blocked
  a_no_adv_on_full:  assert property (@(posedge inclock) (wren && full) |=> write_ptr == $past(write_ptr));
  a_no_adv_on_empty: assert property (@(posedge outclock) (outclocken && empty) |=> read_ptr == $past(read_ptr) && q == $past(q));

  // Coverage
  c_write:   cover property (@(posedge inclock) (wren && !full));
  c_read:    cover property (@(posedge outclock) (outclocken && !empty));
  c_w_wrap:  cover property (@(posedge inclock) (wren && !full && write_ptr==DEPTH-1) |=> write_ptr==0);
  c_r_wrap:  cover property (@(posedge outclock) (outclocken && !empty && read_ptr==DEPTH-1) |=> read_ptr==0);
  c_full:    cover property (@(posedge inclock) full);
  c_empty:   cover property (@(posedge inclock) empty);
  c_empty_to_nonempty: cover property (@(posedge inclock) empty ##1 (wren && !full) ##1 !empty);
  c_nearly_full_to_full: cover property (@(posedge inclock) (dist(write_ptr, read_ptr)==DEPTH-2) ##1 (wren && !full) ##1 full);
  c_drained: cover property (@(posedge outclock) (!empty && outclocken) [*] ##1 empty);

endchecker

bind small_fifo small_fifo_sva sf_sva();