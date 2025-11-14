// Assertions for UART_tx
// Focused, high-quality SVA to check key behavior and provide essential coverage.

bind UART_tx UART_tx_sva ();

module UART_tx_sva;

  // Bring DUT scope signals into this checker via implicit hierarchical reference
  // (bind instantiation occurs in the DUT scope).
  // If your tool requires explicit ports, convert to a ported bind and connect:
  // .clock(clock), .reset(reset), .s_tick(s_tick), .tx_start(tx_start),
  // .data_in(data_in), .tx(tx), .tx_done(tx_done),
  // .current_state(current_state), .next_state(next_state),
  // .B_sent(B_sent), .d_in(d_in)

  // Local aliases (hierarchical from bound scope)
  wire        clock        = clock;
  wire        reset        = reset;
  wire        s_tick       = s_tick;
  wire        tx_start     = tx_start;
  wire [7:0]  data_in      = data_in;
  wire        tx           = tx;
  wire        tx_done      = tx_done;
  wire [1:0]  current_state= current_state;
  wire [1:0]  next_state   = next_state;
  wire [2:0]  B_sent       = B_sent;
  wire [7:0]  d_in         = d_in;

  // State encodings as in DUT
  localparam logic [1:0] IDLE=2'd0, START=2'd1, SEND=2'd2, STOP=2'd3;

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // No X on key signals
  a_no_x:          assert property (!$isunknown({tx, tx_done, current_state, next_state, B_sent, d_in}));

  // Reset puts FSM in IDLE
  a_reset_idle:    assert property (@(posedge clock) reset |-> current_state==IDLE);

  // State must be one-hot-valid (within defined encodings)
  a_state_valid:   assert property (current_state inside {IDLE,START,SEND,STOP});
  a_nstate_valid:  assert property (next_state   inside {IDLE,START,SEND,STOP});

  // IDLE behavior: line high, done low, next_state matches tx_start gating (note: DUT starts on ~tx_start)
  a_idle_outputs:  assert property (current_state==IDLE |-> (tx==1 && tx_done==0));
  a_idle_nstate:   assert property (current_state==IDLE |-> (next_state == (tx_start ? IDLE : START)));

  // START: when s_tick, drive start bit low, clear B_sent, go to SEND
  a_start_tick:    assert property (current_state==START && s_tick |-> (tx==1'b0 && B_sent==3'd0 && next_state==SEND));
  // START: without s_tick, hold tx/B_sent stable
  a_start_hold:    assert property (current_state==START && !s_tick |-> ($stable(tx) && $stable(B_sent)));

  // SEND: on each s_tick for B_sent<7, tx equals d_in[$past(B_sent)], increment counter, stay in SEND
  a_send_tick_mid: assert property (current_state==SEND && s_tick && $past(B_sent)<3'd7
                                    |-> (tx==d_in[$past(B_sent)] && B_sent==$past(B_sent)+3'd1 && next_state==SEND));
  // SEND: on s_tick when last bit (B_sent==7 at start of cycle), drive MSB and go to STOP, counter stays 7
  a_send_tick_last:assert property (current_state==SEND && s_tick && $past(B_sent)==3'd7
                                    |-> (tx==d_in[7] && B_sent==3'd7 && next_state==STOP));
  // SEND: no s_tick => hold tx/counter
  a_send_hold:     assert property (current_state==SEND && !s_tick |-> ($stable(tx) && $stable(B_sent)));
  // SEND: data latch remains stable across entire SEND phase
  a_din_stable:    assert property (current_state==SEND |-> $stable(d_in));

  // STOP: on s_tick, drive stop bit high, assert tx_done, go to IDLE
  a_stop_tick:     assert property (current_state==STOP && s_tick |-> (tx==1'b1 && tx_done==1'b1 && next_state==IDLE));
  // STOP: without s_tick, tx must not change; tx_done cannot be high while waiting
  a_stop_hold_tx:  assert property (current_state==STOP && !s_tick |-> $stable(tx));
  a_stop_done_low: assert property (current_state==STOP && !s_tick |-> !tx_done);

  // tx_done only asserted on STOP s_tick; deasserts next cycle in IDLE
  a_done_origin:   assert property (tx_done |-> (current_state==STOP && s_tick));
  a_done_pulse:    assert property (current_state==STOP && s_tick |-> ##1 (current_state==IDLE && tx_done==0));

  // Line idles high always in IDLE
  a_idle_line_high:assert property (current_state==IDLE |-> tx==1'b1);

  // Minimal end-to-end frame coverage: IDLE -> START(s_tick) -> SEND(last bit) -> STOP(s_tick) -> IDLE, with tx_done pulse
  c_full_frame:    cover property (
                      (current_state==IDLE && !tx_start)
                  ##1 (current_state==START)
                  ##[1:$] (current_state==START && s_tick && tx==1'b0)
                  ##1 (current_state==SEND)
                  ##[1:$] (current_state==SEND && s_tick && $past(B_sent)==3'd7 && tx==d_in[7])
                  ##1 (current_state==STOP)
                  ##[1:$] (current_state==STOP && s_tick && tx==1'b1 && tx_done)
                  ##1 (current_state==IDLE && tx_done==0)
                  );

endmodule