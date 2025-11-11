// Concise SVA checker for fifo. Bind this to the DUT.
// Catches protocol, pointer/count, data, and corner/wrap behavior; includes key covers.
`ifndef FIFO_SVA
`define FIFO_SVA

bind fifo fifo_sva i_fifo_sva();

module fifo_sva (fifo dut);

  localparam int DEPTH = 1024;
  localparam int AW    = $bits(dut.head);

  default clocking cb @(posedge dut.clock); endclocking

  // Accepted transactions
  wire wr_ok = dut.wrreq && !dut.full;
  wire rd_ok = dut.rdreq && !dut.empty;

  // Basic invariants
  a_count_bounds:     assert property (dut.count <= DEPTH);
  a_empty_def:        assert property (dut.empty == (dut.count == 0));
  a_full_def:         assert property (dut.full  == (dut.count == DEPTH));
  a_full_empty_mutex: assert property (!(dut.full && dut.empty));

  // Pointer increment and hold behavior (mod DEPTH)
  a_head_adv: assert property (
    wr_ok |=> dut.head == (($past(dut.head)==DEPTH-1) ? '0 : $past(dut.head)+1)
  );
  a_head_hold: assert property (
    !wr_ok |=> dut.head == $past(dut.head)
  );

  a_tail_adv: assert property (
    rd_ok |=> dut.tail == (($past(dut.tail)==DEPTH-1) ? '0 : $past(dut.tail)+1)
  );
  a_tail_hold: assert property (
    !rd_ok |=> dut.tail == $past(dut.tail)
  );

  // When head == tail, FIFO must be either empty or full (and vice versa)
  a_ptr_eq_implies_state: assert property ((dut.head==dut.tail) |-> (dut.empty || dut.full));
  a_empty_implies_ptr_eq: assert property (dut.empty |-> (dut.head==dut.tail));
  a_full_implies_ptr_eq:  assert property (dut.full  |-> (dut.head==dut.tail));

  // Count update must reflect accepted ops (this will flag the R+W bug)
  a_count_update: assert property (
    1 |-> dut.count == ($past(dut.count) + ($past(wr_ok)?1:0) - ($past(rd_ok)?1:0))
  );

  // Backpressure: no state change on blocked ops
  a_blocked_write_holds: assert property (dut.full  && dut.wrreq |=> dut.head==$past(dut.head) && dut.count==$past(dut.count));
  a_blocked_read_holds:  assert property (dut.empty && dut.rdreq |=> dut.tail==$past(dut.tail) && dut.count==$past(dut.count) && dut.q==$past(dut.q));

  // Data path: write stores correct data; read returns stored data; q holds when no read
  a_store_correct: assert property ($past(wr_ok) |-> dut.fifo[$past(dut.head)] == $past(dut.data));
  a_read_returns:  assert property ($past(rd_ok) |-> dut.q == $past(dut.fifo[$past(dut.tail)]));
  a_q_holds_no_read: assert property (!rd_ok |=> dut.q == $past(dut.q));

  // Coverage: fill, drain, simultaneous R/W, and wrap-around events
  c_fill_to_full:  cover property (dut.empty ##1 (wr_ok)[*DEPTH] ##1 dut.full);
  c_drain_to_empty:cover property (dut.full  ##1 (rd_ok)[*DEPTH] ##1 dut.empty);
  c_simul_rw:      cover property (wr_ok && rd_ok);
  c_head_wrap:     cover property ((dut.head==DEPTH-1) && wr_ok ##1 (dut.head==0));
  c_tail_wrap:     cover property ((dut.tail==DEPTH-1) && rd_ok ##1 (dut.tail==0));
  c_boundary_simul_near_full:  cover property ((dut.count==DEPTH-1) && wr_ok && rd_ok);
  c_boundary_simul_near_empty: cover property ((dut.count==1)        && wr_ok && rd_ok);

endmodule

`endif