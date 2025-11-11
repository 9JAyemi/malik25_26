// SVA for fifo_ctr
// Bind this checker to the DUT. Focused, high-signal-coverage and concise.

module fifo_ctr_sva #(
  parameter int numOfRam = 32,
  parameter int W        = 5
)(
  input  logic              clk, rst_n,
  input  logic              push, pop,

  input  logic [1:0]        state,
  input  logic [W-1:0]      head, tail,
  input  logic              head_plus, tail_plus,

  input  logic              do_idle, do_pop, do_push, do_push_pop,

  input  logic              empty, almost_empty, full, almost_full,
  input  logic              error, cen, wen, oen,
  input  logic [W-1:0]      addr
);

  localparam logic [1:0] S_EMPTY   = 2'b00;
  localparam logic [1:0] S_BETWEEN = 2'b01;
  localparam logic [1:0] S_READOUT = 2'b10;
  localparam logic [1:0] S_FULL    = 2'b11;

  default clocking cb @(posedge clk); endclocking
  // General properties disabled during reset except where noted
  `define DIS disable iff (!rst_n)

  // Reset values
  assert property (@cb !rst_n |-> (state==S_EMPTY && head==0 && tail==0));

  // Basic decodes
  assert property (`DIS (do_idle     == (!push && !pop)));
  assert property (`DIS (do_pop      == (!push &&  pop)));
  assert property (`DIS (do_push     == ( push && !pop)));
  assert property (`DIS (do_push_pop == ( push &&  pop)));
  assert property (`DIS $onehot({do_idle,do_pop,do_push,do_push_pop}));

  // Ranges
  assert property (`DIS (head < numOfRam && tail < numOfRam && addr < numOfRam));

  // Almost flags (modulo ring)
  assert property (`DIS (almost_full  == ((head + W'(1)) == tail)));
  assert property (`DIS (almost_empty == ((tail + W'(1)) == head)));

  // Head/Tail update
  assert property (@cb (rst_n && $past(rst_n)) |-> head == ($past(head_plus) ? ($past(head)+W'(1)) : $past(head)));
  assert property (@cb (rst_n && $past(rst_n)) |-> tail == ($past(tail_plus) ? ($past(tail)+W'(1)) : $past(tail)));

  // Plus strobes
  assert property (`DIS ((state==S_READOUT) == tail_plus));
  assert property (`DIS (head_plus |-> ((state==S_EMPTY || state==S_BETWEEN) && do_push && !do_push_pop)));
  assert property (`DIS (((state==S_EMPTY || state==S_BETWEEN) && do_push && !do_push_pop) |-> head_plus));

  // Next-state map
  assert property (@cb `DIS ($past(rst_n) && $past(state)==S_EMPTY)
                   |-> state == ($past(do_push) ? S_BETWEEN : S_EMPTY));

  assert property (@cb `DIS ($past(rst_n) && $past(state)==S_BETWEEN)
                   |-> state == ($past(do_pop) ? S_READOUT
                                  : ($past(do_push) ? ($past(almost_full) ? S_FULL : S_BETWEEN)
                                                    : S_BETWEEN)));

  assert property (@cb `DIS ($past(rst_n) && $past(state)==S_READOUT)
                   |-> state == ($past(almost_empty) ? S_EMPTY : S_BETWEEN));

  assert property (@cb `DIS ($past(rst_n) && $past(state)==S_FULL)
                   |-> state == ($past(do_pop) ? S_READOUT : S_FULL));

  // Error semantics
  // EMPTY
  assert property (`DIS ((state==S_EMPTY   && (do_pop || do_push_pop)) |->  error));
  assert property (`DIS ((state==S_EMPTY   && (do_idle || do_push))    |-> !error));
  // BETWEEN
  assert property (`DIS ((state==S_BETWEEN &&  do_push_pop)            |->  error));
  assert property (`DIS ((state==S_BETWEEN && (do_idle || do_push || do_pop)) |-> !error));
  // READOUT
  assert property (`DIS ((state==S_READOUT && (do_push || do_pop))     |->  error));
  assert property (`DIS ((state==S_READOUT &&  do_idle)                |-> !error));
  // FULL
  assert property (`DIS ((state==S_FULL    && (do_push || do_push_pop))|->  error));
  assert property (`DIS ((state==S_FULL    && (do_idle || do_pop))     |-> !error));

  // Write enable/address rules
  assert property (`DIS (((state==S_EMPTY || state==S_BETWEEN) && do_push && !do_push_pop)
                         |-> (wen==1'b0 && addr==head)));
  assert property (`DIS (wen==1'b0 |-> ((state==S_EMPTY || state==S_BETWEEN) && do_push && !do_push_pop && addr==head)));

  // Pop address usage
  assert property (`DIS ((state==S_BETWEEN && do_pop) |-> addr==tail));
  assert property (`DIS ((state==S_FULL    && do_pop) |-> addr==tail));

  // Constant controls
  assert property (`DIS (oen==1'b0));
  assert property (`DIS (cen==1'b0));

  // State->flag expectations (intent)
  assert property (`DIS ((state==S_EMPTY) |-> empty));
  assert property (`DIS ((state==S_FULL)  |-> full));

  // Covers
  cover property (@cb rst_n && state==S_EMPTY);
  cover property (@cb rst_n && state==S_BETWEEN);
  cover property (@cb rst_n && state==S_READOUT);
  cover property (@cb rst_n && state==S_FULL);

  cover property (@cb rst_n && state==S_EMPTY  ##1 do_push ##1 state==S_BETWEEN ##[1:$] state==S_FULL);
  cover property (@cb rst_n && state==S_FULL   ##1 do_pop  ##1 state==S_READOUT ##1 state==S_EMPTY);

  cover property (@cb rst_n && state==S_EMPTY   && do_pop      && error);
  cover property (@cb rst_n && state==S_FULL    && do_push     && error);
  cover property (@cb rst_n && state==S_READOUT && do_push     && error);
  cover property (@cb rst_n && do_push_pop && error);

  cover property (@cb rst_n && (head==numOfRam-1) &&
                  (state==S_BETWEEN || state==S_EMPTY) && do_push && !do_push_pop ##1 head==0);
  cover property (@cb rst_n && (tail==numOfRam-1) &&
                  state==S_READOUT ##1 tail==0);

  cover property (@cb rst_n && almost_full  && state==S_BETWEEN);
  cover property (@cb rst_n && almost_empty && state==S_READOUT);

endmodule

// Bind to DUT
bind fifo_ctr fifo_ctr_sva #(.numOfRam(numOfRam)) fifo_ctr_sva_i (
  .clk(clk), .rst_n(rst_n), .push(push), .pop(pop),
  .state(state), .head(head), .tail(tail),
  .head_plus(head_plus), .tail_plus(tail_plus),
  .do_idle(do_idle), .do_pop(do_pop), .do_push(do_push), .do_push_pop(do_push_pop),
  .empty(empty), .almost_empty(almost_empty), .full(full), .almost_full(almost_full),
  .error(error), .cen(cen), .wen(wen), .oen(oen), .addr(addr)
);