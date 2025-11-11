// SVA bind file for ll8_to_txmac
// Focused, high-quality checks of FSM, outputs, and key behaviors.

bind ll8_to_txmac ll8_to_txmac_sva i_ll8_to_txmac_sva
(
  .clk(clk), .reset(reset), .clear(clear),
  .ll_data(ll_data), .ll_sof(ll_sof), .ll_eof(ll_eof), .ll_src_rdy(ll_src_rdy), .ll_dst_rdy(ll_dst_rdy),
  .tx_data(tx_data), .tx_valid(tx_valid), .tx_error(tx_error), .tx_ack(tx_ack),
  .xfer_state(xfer_state)
);

module ll8_to_txmac_sva
(
  input logic                 clk, reset, clear,
  input logic [7:0]           ll_data,
  input logic                 ll_sof, ll_eof, ll_src_rdy, ll_dst_rdy,
  input logic [7:0]           tx_data,
  input logic                 tx_valid, tx_error, tx_ack,
  input logic [2:0]           xfer_state
);
  // Mirror DUT encoding
  localparam int XFER_IDLE      = 0;
  localparam int XFER_ACTIVE    = 1;
  localparam int XFER_WAIT1     = 2;
  localparam int XFER_UNDERRUN  = 3;
  localparam int XFER_DROP      = 4;

  // Default clocking/reset
  default clocking cb @(posedge clk); endclocking
  `define DIS disable iff (reset || clear)

  // Legal state encoding
  assert property (`DIS (xfer_state inside {XFER_IDLE,XFER_ACTIVE,XFER_WAIT1,XFER_UNDERRUN,XFER_DROP}));

  // Synchronous reset/clear
  assert property ((reset || clear) |=> xfer_state == XFER_IDLE);

  // FSM next-state rules
  assert property (`DIS (xfer_state==XFER_IDLE  &&  tx_ack                    |=> xfer_state==XFER_ACTIVE));
  assert property (`DIS (xfer_state==XFER_IDLE  && !tx_ack                    |=> xfer_state==XFER_IDLE));
  assert property (`DIS (xfer_state==XFER_ACTIVE&& !ll_src_rdy                |=> xfer_state==XFER_UNDERRUN));
  assert property (`DIS (xfer_state==XFER_ACTIVE&&  ll_src_rdy &&  ll_eof     |=> xfer_state==XFER_WAIT1));
  assert property (`DIS (xfer_state==XFER_ACTIVE&&  ll_src_rdy && !ll_eof     |=> xfer_state==XFER_ACTIVE));
  assert property (`DIS (xfer_state==XFER_WAIT1                               |=> xfer_state==XFER_IDLE));
  assert property (`DIS (xfer_state==XFER_UNDERRUN                            |=> xfer_state==XFER_DROP));
  assert property (`DIS (xfer_state==XFER_DROP && !ll_eof                     |=> xfer_state==XFER_DROP));
  assert property (`DIS (xfer_state==XFER_DROP &&  ll_eof                     |=> xfer_state==XFER_IDLE));

  // Entry (predecessor) checks for key states
  assert property (`DIS (xfer_state==XFER_WAIT1     |-> $past(xfer_state==XFER_ACTIVE && ll_src_rdy && ll_eof)));
  assert property (`DIS (xfer_state==XFER_UNDERRUN  |-> $past(xfer_state==XFER_ACTIVE && !ll_src_rdy)));
  assert property (`DIS (xfer_state==XFER_DROP      |-> $past(xfer_state==XFER_UNDERRUN) ||
                                          $past(xfer_state==XFER_DROP && !ll_eof)));

  // Output equivalences to spec
  assert property (`DIS (ll_dst_rdy == ((xfer_state==XFER_ACTIVE) || tx_ack || (xfer_state==XFER_DROP))));
  assert property (`DIS (tx_valid   == ((ll_src_rdy && (xfer_state==XFER_IDLE)) || (xfer_state==XFER_ACTIVE))));
  assert property (`DIS (tx_error   == (xfer_state==XFER_UNDERRUN)));
  assert property (`DIS (tx_data    == ll_data));

  // Sanity relationships implied by outputs
  assert property (`DIS (tx_error |-> !tx_valid));      // UNDERRUN implies no valid
  assert property (`DIS ((xfer_state inside {XFER_WAIT1,XFER_UNDERRUN,XFER_DROP}) |-> !tx_valid));

  // Coverage: visit all states
  cover property (`DIS (xfer_state==XFER_IDLE));
  cover property (`DIS (xfer_state==XFER_ACTIVE));
  cover property (`DIS (xfer_state==XFER_WAIT1));
  cover property (`DIS (xfer_state==XFER_UNDERRUN));
  cover property (`DIS (xfer_state==XFER_DROP));

  // Coverage: normal frame flow
  cover property (`DIS (xfer_state==XFER_IDLE && tx_ack
                        ##1 xfer_state==XFER_ACTIVE
                        ##[1:$] (xfer_state==XFER_ACTIVE && ll_src_rdy && ll_eof)
                        ##1 xfer_state==XFER_WAIT1 ##1 xfer_state==XFER_IDLE));

  // Coverage: underrun -> drop -> recover on EOF
  cover property (`DIS (xfer_state==XFER_IDLE && tx_ack
                        ##1 xfer_state==XFER_ACTIVE
                        ##[0:$] (xfer_state==XFER_ACTIVE && !ll_src_rdy)
                        ##1 xfer_state==XFER_UNDERRUN ##1 xfer_state==XFER_DROP
                        ##[1:$] (xfer_state==XFER_DROP && ll_eof)
                        ##1 xfer_state==XFER_IDLE));

  // Coverage: tx_valid asserted in IDLE due to ll_src_rdy
  cover property (`DIS (xfer_state==XFER_IDLE && ll_src_rdy && tx_valid));

  // Coverage: extended ACTIVE run without EOF
  cover property (`DIS (xfer_state==XFER_ACTIVE && ll_src_rdy && !ll_eof
                        ##1 xfer_state==XFER_ACTIVE && ll_src_rdy && !ll_eof
                        ##1 xfer_state==XFER_ACTIVE && ll_src_rdy && !ll_eof));

endmodule