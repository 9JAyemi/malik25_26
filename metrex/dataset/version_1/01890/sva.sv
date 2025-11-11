// SVA checker for altpcierd_tx_ecrc_ctl_fifo
// Focused, concise properties with essential coverage

module altpcierd_tx_ecrc_ctl_fifo_sva (
  input  logic        aclr,
  input  logic        clock,
  input  logic  [0:0] data,
  input  logic        rdreq,
  input  logic        wrreq,
  input  logic        almost_full,
  input  logic        empty,
  input  logic        full,
  input  logic  [0:0] q
);

  default clocking cb @(posedge clock); endclocking
  default disable iff (aclr);

  // Asynchronous reset effects
  assert property (@(posedge aclr) q == 1'b0);
  assert property (aclr |-> q == 1'b0);

  // Constant outputs
  assert property (full == 1'b0);
  assert property (almost_full == 1'b0);

  // Empty flag definition matches q
  assert property (empty === (q == 1'b0));

  // Write-only cycle updates q to data (since full is always 0)
  assert property ((wrreq && !rdreq) |=> q == $past(data));

  // Read when not empty forces X (by design)
  assert property ((rdreq && !empty) |=> $isunknown(q));

  // Simultaneous read & write forces X (by design)
  assert property ((wrreq && rdreq) |=> $isunknown(q));

  // Idle holds value
  assert property ((!wrreq && !rdreq) |=> q == $past(q));

  // Read of empty without write holds value
  assert property ((rdreq && empty && !wrreq) |=> q == $past(q));

  // Empty flag reflects post-write q
  assert property ((wrreq && !rdreq) |=> empty === ($past(data) == 1'b0));

  // Coverage: reset, write, illegal ops, idle
  cover property ($rose(aclr));
  cover property ((wrreq && !rdreq) ##1 (q == $past(data)) ##0 (empty === ($past(data) == 1'b0)));
  cover property ((rdreq && !empty) ##1 $isunknown(q));
  cover property ((wrreq && rdreq) ##1 $isunknown(q));
  cover property ((!wrreq && !rdreq) ##1 (q == $past(q)));

endmodule

bind altpcierd_tx_ecrc_ctl_fifo altpcierd_tx_ecrc_ctl_fifo_sva sva_i (
  .aclr(aclr),
  .clock(clock),
  .data(data),
  .rdreq(rdreq),
  .wrreq(wrreq),
  .almost_full(almost_full),
  .empty(empty),
  .full(full),
  .q(q)
);