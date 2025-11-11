// SVA checker for module transmision
module transmision_sva #(
  parameter int COUNT = 8
)(
  input  logic        clk_div,
  input  logic        enable,
  input  logic [7:0]  dout,
  input  logic        busy,
  input  logic        done,
  input  logic        tx,
  input  logic [1:0]  state,
  input  logic [2:0]  bitpos,
  input  logic [7:0]  data
);
  localparam [1:0] STATE_IDLE  = 2'b00;
  localparam [1:0] STATE_START = 2'b01;
  localparam [1:0] STATE_DATA  = 2'b10;
  localparam [1:0] STATE_STOP  = 2'b11;

  initial assert (COUNT >= 1 && COUNT <= 8)
    else $error("COUNT must be 1..8");

  default clocking cb @(posedge clk_div); endclocking

  // X/validity checks
  a_known_all:        assert property (!$isunknown({state,bitpos,data,tx,done,busy}));  
  a_state_legal:      assert property (state inside {STATE_IDLE,STATE_START,STATE_DATA,STATE_STOP});

  // Busy definition
  a_busy_def:         assert property (busy == (state != STATE_IDLE));

  // IDLE behavior
  a_idle_outputs:     assert property (state==STATE_IDLE |-> (tx==1 && done==0));
  a_idle_hold_no_en:  assert property (state==STATE_IDLE && !enable |=> state==STATE_IDLE);

  // Enable handshake and latching
  a_en_to_start:      assert property (state==STATE_IDLE && enable |=> state==STATE_START && data==$past(dout) && bitpos==0 && busy);
  a_start_one_cycle:  assert property (state==STATE_START |-> tx==0);
  a_start_to_data:    assert property (state==STATE_START |=> state==STATE_DATA);

  // DATA behavior
  a_data_tx_bit:      assert property (state==STATE_DATA |-> tx == data[bitpos]);
  a_data_incr:        assert property (state==STATE_DATA && bitpos < COUNT-1 |=> state==STATE_DATA && bitpos==$past(bitpos)+1);
  a_data_last:        assert property (state==STATE_DATA && bitpos == COUNT-1 |=> state==STATE_STOP && bitpos==$past(bitpos));
  a_bitpos_bound:     assert property (bitpos < COUNT);
  a_data_stable_busy: assert property ((state!=STATE_IDLE) |-> $stable(data));

  // STOP behavior and done pulse
  a_stop_outputs:     assert property (state==STATE_STOP |-> (tx==1 && done==1 && busy));
  a_stop_to_idle:     assert property (state==STATE_STOP |=> state==STATE_IDLE && done==0);
  a_done_only_in_stop:assert property (done |-> state==STATE_STOP);
  a_done_one_cycle:   assert property (done |=> !done);
  a_done_busy_align:  assert property (done |=> !busy);

  // Latency from enable to done
  a_done_latency:     assert property (state==STATE_IDLE && enable |=> ##(COUNT+1) done);

  // Full-frame coverage (idle->start->data[count]->stop->idle)
  c_full_frame: cover property (
    state==STATE_IDLE && enable ##1
    state==STATE_START ##1
    state==STATE_DATA [*COUNT] ##1
    state==STATE_STOP ##1
    state==STATE_IDLE
  );

  // Back-to-back frames (enable still asserted)
  c_back2back: cover property (
    state==STATE_IDLE && enable ##1
    state==STATE_START ##1
    state==STATE_DATA [*COUNT] ##1
    state==STATE_STOP ##1
    state==STATE_IDLE && enable ##1
    state==STATE_START
  );

  // Data value coverage examples
  c_all_zero: cover property (state==STATE_IDLE && enable && dout==8'h00);
  c_all_one:  cover property (state==STATE_IDLE && enable && dout==8'hFF);

endmodule

// Bind into DUT (connect internal regs)
bind transmision transmision_sva #(.COUNT(count)) u_transmision_sva (
  .clk_div(clk_div),
  .enable(enable),
  .dout(dout),
  .busy(busy),
  .done(done),
  .tx(tx),
  .state(state),
  .bitpos(bitpos),
  .data(data)
);