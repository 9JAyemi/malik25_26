// SVA for intern_sync: concise, high-quality checks and key coverage
module intern_sync_sva
(
  input  logic        clk,
  input  logic        rstn,
  input  logic        rc_is_idle,
  input  logic        rc_reqn,
  input  logic        rc_ackn,
  input  logic [1:0]  state_c
);
  // Mirror DUT encodings (2-bit)
  localparam logic [1:0] RC_Idle   = 2'd0;
  localparam logic [1:0] RC_ReqAck = 2'd1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rstn);

  // Basic sanity/knownness
  a_knowns:         assert property (!$isunknown({state_c, rc_ackn, rc_reqn, rc_is_idle})));
  a_reset_to_idle:  assert property (!rstn |-> state_c == RC_Idle);
  a_state_legal:    assert property (state_c inside {RC_Idle, RC_ReqAck});

  // FSM transition correctness
  a_idle_hold:      assert property ((state_c==RC_Idle   &&  rc_reqn) |=> state_c==RC_Idle);
  a_idle_to_req:    assert property ((state_c==RC_Idle   && !rc_reqn) |=> state_c==RC_ReqAck);
  a_req_hold:       assert property ((state_c==RC_ReqAck && !rc_is_idle) |=> state_c==RC_ReqAck);
  a_req_to_idle:    assert property ((state_c==RC_ReqAck &&  rc_is_idle) |=> state_c==RC_Idle);
  a_enter_req_from_idle: assert property ($rose(state_c==RC_ReqAck) |-> $past(state_c==RC_Idle && !rc_reqn));

  // Output behavior (ack is active-low pulse only when RC_ReqAck && rc_is_idle)
  a_ack_low_cond:   assert property (rc_ackn==0 |-> (state_c==RC_ReqAck && rc_is_idle));
  a_ack_low_needed: assert property ((state_c==RC_ReqAck && rc_is_idle) |-> rc_ackn==0);
  a_ack_high_idle:  assert property ((state_c==RC_Idle) |-> rc_ackn==1);
  a_ack_high_when_busy: assert property ((state_c==RC_ReqAck && !rc_is_idle) |-> rc_ackn==1);
  a_ack_one_cycle:  assert property (rc_ackn==0 |=> rc_ackn==1);
  a_ack_implies_next_idle: assert property (rc_ackn==0 |=> state_c==RC_Idle);

  // Key functional coverage
  // 1) Request then stall in RC_ReqAck, then ack pulse, return to Idle
  c_req_stall_then_ack: cover property (
    (state_c==RC_Idle && !rc_reqn)
    ##1 (state_c==RC_ReqAck && !rc_is_idle)[*1:$]
    ##1 (state_c==RC_ReqAck && rc_is_idle && rc_ackn==0)
    ##1 (state_c==RC_Idle)
  );

  // 2) Back-to-back accepts when request held low and resource idle (multiple ack pulses)
  c_back_to_back_acks: cover property (
    (state_c==RC_Idle && !rc_reqn)
    ##1 (state_c==RC_ReqAck && rc_is_idle && rc_ackn==0)
    ##1 (state_c==RC_Idle && !rc_reqn)
    ##1 (state_c==RC_ReqAck && rc_is_idle && rc_ackn==0)
  );
endmodule

// Bind into DUT
bind intern_sync intern_sync_sva i_intern_sync_sva(.clk(clk), .rstn(rstn),
  .rc_is_idle(rc_is_idle), .rc_reqn(rc_reqn), .rc_ackn(rc_ackn), .state_c(state_c));