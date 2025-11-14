// SVA checker for fifo
module fifo_sva;
  // Infer params from DUT
  localparam int AW    = $bits(head);
  localparam int DW    = $bits(q);
  localparam int DEPTH = 1<<AW;

  default clocking cb @(posedge clock); endclocking

  bit started;
  initial started = 0;
  always_ff @(posedge clock) started <= 1;
  default disable iff (!started);

  // Basic sanity
  assert property (!$isunknown({empty, full, q, head, tail, count}));
  assert property (head < DEPTH && tail < DEPTH);

  // Flag correctness
  assert property (empty == (count == 0));
  assert property (full  == (count == DEPTH));

  // Pointer updates
  assert property ((wrreq && !full) |=> head == (($past(head)==DEPTH-1) ? '0 : $past(head)+1));
  assert property (!(wrreq && !full) |=> head == $past(head));
  assert property ((rdreq && !empty) |=> tail == (($past(tail)==DEPTH-1) ? '0 : $past(tail)+1));
  assert property (!(rdreq && !empty) |=> tail == $past(tail));

  // Count updates
  assert property ((wrreq && !full) &&  (rdreq && !empty) |=> count == $past(count));
  assert property ((wrreq && !full) && !(rdreq && !empty) |=> count == $past(count)+1);
  assert property ((rdreq && !empty) && !(wrreq && !full) |=> count == $past(count)-1);
  assert property (!(wrreq && !full) && !(rdreq && !empty) |=> count == $past(count));

  // Geometry consistency
  assert property ((count == 0)      |-> head == tail);
  assert property ((count == DEPTH)  |-> head == tail);
  assert property ((count > 0 && count < DEPTH && head >= tail) |-> count == head - tail);
  assert property ((count > 0 && count < DEPTH && head <  tail) |-> count == DEPTH - (tail - head));

  // Blocked ops don't change state
  assert property (full  && !rdreq |=> head == $past(head) && count == $past(count));
  assert property (empty && !wrreq |=> tail == $past(tail) && count == $past(count));

  // q behavior
  assert property (!(rdreq && !empty) |=> $stable(q));

  // Data integrity (shadow model)
  logic [DW-1:0] shadow_mem [0:DEPTH-1];
  always_ff @(posedge clock)
    if (wrreq && !full) shadow_mem[head] <= data;
  assert property ((rdreq && !empty) |=> q == $past(shadow_mem[$past(tail)]));

  // Liveness: filling must lead to full
  sequence wr_only; wrreq && !full && !(rdreq && !empty); endsequence
  assert property (empty ##1 wr_only[*DEPTH] |=> full);

  // Coverage
  cover property (wrreq && !full);
  cover property (rdreq && !empty);
  cover property (wrreq && !full && rdreq && !empty);
  cover property ($past(head)==DEPTH-1 && wrreq && !full |=> head==0);
  cover property ($past(tail)==DEPTH-1 && rdreq && !empty |=> tail==0);
  cover property (empty ##1 wr_only[*1:4] ##1 !empty);
  cover property (empty ##1 wr_only[*DEPTH] ##1 full);
  cover property (full ##1 rdreq && !empty ##1 !full);
endmodule

bind fifo fifo_sva u_fifo_sva();