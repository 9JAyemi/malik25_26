// SVA for sync_fifo
// Bind this into the DUT for assertions and coverage.

module sync_fifo_sva #(parameter DWIDTH=16, DEPTH=8) ();

  // Access DUT scope via bind
  // DUT signals (implicit via bind scope):
  // clk, res_n, d_in, shift_in, shift_out, d_out, full, empty, almost_full, almost_empty
  // buffer, fill_level, read_pointer, write_pointer

  default clocking cb @(posedge clk); endclocking
  default disable iff (!res_n)

  // Helpers
  let fl      = $unsigned(fill_level);
  let rp      = $unsigned(read_pointer);
  let wp      = $unsigned(write_pointer);
  let pop_e   = (shift_out && !empty);
  let push_e  = (shift_in  && !full  && !pop_e); // else-if priority: pop wins

  // Reset values (asynchronous)
  assert property (@(negedge res_n)
                   1 |-> (d_out=='0 && fill_level=='0 && read_pointer=='0 &&
                          write_pointer=='0 && empty && !full));

  // Bounds and basic invariants
  assert property (fl <= DEPTH);
  assert property (rp < DEPTH);
  assert property (wp < DEPTH);
  assert property (!(full && empty));
  assert property (empty == (fl == 0));
  assert property (full  == (fl == DEPTH));
  assert property (almost_full  == (fl >= (DEPTH-1)));
  assert property (almost_empty == (fl <= 1));

  // Fill-level step semantics
  assert property (pop_e    |=> fl == $past(fl)-1);
  assert property (push_e   |=> fl == $past(fl)+1);
  assert property ((!pop_e && !push_e) |=> fl == $past(fl));
  // No multi-step jumps
  assert property ( (fl == $past(fl)) ||
                    (fl == $past(fl)+1) ||
                    (fl == $past(fl)-1) );

  // Pointer update semantics and stability when not active
  assert property (pop_e  |=> read_pointer  == $past(read_pointer)+1);
  assert property (push_e |=> write_pointer == $past(write_pointer)+1);

  assert property ((!pop_e)  |=> (pop_e  || read_pointer  == $past(read_pointer)));
  assert property ((!push_e) |=> (push_e || write_pointer == $past(write_pointer)));

  // Priority on simultaneous shift_in & shift_out (pop wins when not empty)
  assert property ((shift_in && shift_out && !empty)
                   |=> (read_pointer == $past(read_pointer)+1) &&
                       (write_pointer == $past(write_pointer)) &&
                       (fl == $past(fl)-1));

  // Flag transitions consistent with count edges
  assert property ($rose(full)  |-> fl == DEPTH);
  assert property ($fell(full)  |-> fl <  DEPTH);
  assert property ($rose(empty) |-> fl == 0);
  assert property ($fell(empty) |-> fl >  0);

  // d_out stability when no pop; allow change if next cycle is a pop
  assert property ((!pop_e) |=> (pop_e || d_out == $past(d_out)));

  // Underflow/overflow attempts do not change state (except flags already invariant)
  assert property ((shift_out && empty) |=> (read_pointer == $past(read_pointer)) &&
                                          (fl == $past(fl)));
  assert property ((shift_in && full)   |=> (write_pointer == $past(write_pointer)) &&
                                          (fl == $past(fl)));

  // Coverage
  cover property ($rose(res_n));
  cover property ($rose(almost_full));
  cover property ($rose(full));
  cover property ($rose(almost_empty));
  cover property ($rose(empty));
  cover property (shift_in && full);      // overflow attempt
  cover property (shift_out && empty);    // underflow attempt
  cover property (shift_in && shift_out && !empty); // priority case
  cover property (fl == DEPTH);
  cover property (fl == 0);

endmodule

bind sync_fifo sync_fifo_sva #(.DWIDTH(DWIDTH), .DEPTH(DEPTH)) u_sync_fifo_sva();