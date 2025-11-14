// synthesis translate_off
// SVA checker for my_fifo/scfifo
module fifo_sva #(parameter int WIDTH=34, parameter int DEPTHW=10)
(
  input logic                 clock,
  input logic                 aclr,
  input logic [WIDTH-1:0]     data,
  input logic                 rdreq,
  input logic                 wrreq,
  input logic [WIDTH-1:0]     q,
  input logic [DEPTHW-1:0]    usedw
);

  localparam int unsigned MAX = (1<<DEPTHW)-1;

  default clocking cb @(posedge clock); endclocking
  default disable iff (aclr);

  // Async reset effects (checked both at posedge aclr and at following clocks)
  assert property (@(posedge aclr) 1 |-> (q=='0 && usedw=='0));
  assert property (@(posedge clock) aclr |-> (q=='0 && usedw=='0));
  assert property (@(posedge clock) $fell(aclr) |-> (q=='0 && usedw=='0));

  // usedw delta semantics
  assert property ((wrreq && !rdreq && $past(!aclr)) |=> usedw == $past(usedw)+1);
  assert property ((rdreq && !wrreq && $past(!aclr)) |=> usedw == $past(usedw)-1);
  assert property ((wrreq && rdreq  && $past(!aclr)) |=> usedw == $past(usedw));
  assert property ((!wrreq && !rdreq && $past(!aclr)) |=> usedw == $past(usedw));

  // usedw never changes by more than 1
  assert property ($past(!aclr) |-> (usedw == $past(usedw) ||
                                     usedw == $past(usedw)+1 ||
                                     usedw == $past(usedw)-1));

  // Underflow/overflow protection (no rd-only at empty, no wr-only at full)
  assert property ((rdreq && !wrreq) |-> $past(usedw) > 0);
  assert property ((wrreq && !rdreq) |-> $past(usedw) < MAX);

  // Bounds
  assert property (usedw <= MAX);

  // q update semantics
  assert property ((wrreq && !rdreq && $past(!aclr)) |=> q == $past(data));
  assert property ((rdreq && !wrreq && $past(!aclr)) |=> q == '0);
  assert property ((wrreq && rdreq  && $past(!aclr)) |=> q == '0);
  assert property ((!wrreq && !rdreq && $past(!aclr)) |=> q == $past(q));

  // When empty, output must be zero
  assert property (usedw == 0 |-> q == '0);

  // No X on outputs
  assert property (!$isunknown({q,usedw}));

  // Coverage
  cover property (@(posedge aclr) 1);                     // async reset hit
  cover property (usedw == 0);                            // empty reached
  cover property (usedw == MAX);                          // full reached
  cover property (wrreq && !rdreq);                       // write-only
  cover property (rdreq && !wrreq);                       // read-only
  cover property (wrreq && rdreq);                        // simultaneous R/W
  cover property ($past(usedw)==0 && wrreq && !rdreq |=> usedw==1);           // first write from empty
  cover property ($past(usedw)==MAX && rdreq && !wrreq |=> usedw==MAX-1);     // read from full
  cover property (wrreq && !rdreq |=> q == $past(data));  // data captured on write
  cover property ((rdreq && !wrreq) |=> q == '0);         // data cleared on read

endmodule

// Bind to the FIFO implementation
bind scfifo fifo_sva #(.WIDTH(34), .DEPTHW(10)) scfifo_sva_i (
  .clock(clock),
  .aclr(aclr),
  .data(data),
  .rdreq(rdreq),
  .wrreq(wrreq),
  .q(q),
  .usedw(usedw)
);
// synthesis translate_on