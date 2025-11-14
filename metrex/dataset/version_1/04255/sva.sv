// SVA for fsm_using_single_always
module fsm_using_single_always_sva
  #(parameter int SIZE=3,
    parameter logic [SIZE-1:0] IDLE=3'b001,
    parameter logic [SIZE-1:0] GNT0=3'b010,
    parameter logic [SIZE-1:0] GNT1=3'b100)
(
  input logic                   clock,
  input logic                   reset,
  input logic                   req_0,
  input logic                   req_1,
  input logic                   gnt_0,
  input logic                   gnt_1,
  input logic [SIZE-1:0]        state
);

  default clocking cb @(posedge clock); endclocking

  // Reset behavior
  a_reset_state: assert property (reset |=> (state==IDLE && !gnt_0 && !gnt_1));

  // Legal/one-hot state
  a_legal_state: assert property (disable iff (reset)
                                  (state inside {IDLE,GNT0,GNT1}) && $onehot(state));

  // Mutual exclusion of grants
  a_gnt_mutex: assert property (disable iff (reset) !(gnt_0 && gnt_1));

  // State-to-grant consistency
  a_idle_no_grant:  assert property (disable iff (reset) (state==IDLE) |-> (!gnt_0 && !gnt_1));
  a_gnt0_consist:   assert property (disable iff (reset) (state==GNT0) |-> ( gnt_0 && !gnt_1));
  a_gnt1_consist:   assert property (disable iff (reset) (state==GNT1) |-> (!gnt_0 &&  gnt_1));

  // IDLE transitions and priority
  a_idle_req0:      assert property (disable iff (reset) (state==IDLE && req_0) |=> (state==GNT0 && gnt_0));
  a_idle_req1:      assert property (disable iff (reset) (state==IDLE && !req_0 && req_1) |=> (state==GNT1 && gnt_1));
  a_idle_none:      assert property (disable iff (reset) (state==IDLE && !req_0 && !req_1) |=> (state==IDLE && !gnt_0 && !gnt_1));
  a_idle_prio:      assert property (disable iff (reset) (state==IDLE && req_0 && req_1) |=> (state==GNT0 && gnt_0 && !gnt_1));

  // GNT0 behavior
  a_gnt0_hold:      assert property (disable iff (reset) (state==GNT0 && req_0) |=> (state==GNT0 && gnt_0));
  a_gnt0_release:   assert property (disable iff (reset) (state==GNT0 && !req_0) |=> (state==IDLE && !gnt_0));

  // GNT1 behavior
  a_gnt1_hold:      assert property (disable iff (reset) (state==GNT1 && req_1) |=> (state==GNT1 && gnt_1));
  a_gnt1_release:   assert property (disable iff (reset) (state==GNT1 && !req_1) |=> (state==IDLE && !gnt_1));

  // Grant edge-cause checks
  a_gnt0_rose_cause: assert property (disable iff (reset) $rose(gnt_0) |-> $past(state==IDLE && req_0));
  a_gnt1_rose_cause: assert property (disable iff (reset) $rose(gnt_1) |-> $past(state==IDLE && req_1));
  a_gnt0_fell_cause: assert property (disable iff (reset) $fell(gnt_0) |-> $past(state==GNT0 && !req_0));
  a_gnt1_fell_cause: assert property (disable iff (reset) $fell(gnt_1) |-> $past(state==GNT1 && !req_1));

  // Coverage
  c_state_idle:        cover property (disable iff (reset) state==IDLE);
  c_state_gnt0:        cover property (disable iff (reset) state==GNT0);
  c_state_gnt1:        cover property (disable iff (reset) state==GNT1);
  c_prio_take_0:       cover property (disable iff (reset) (state==IDLE && req_0 && req_1) |=> state==GNT0);
  c_flow_0_to_1:       cover property (disable iff (reset)
                                       (state==GNT0 && !req_0 && req_1) ##1 state==IDLE ##1 state==GNT1);
  c_flow_1_to_0:       cover property (disable iff (reset)
                                       (state==GNT1 && !req_1 && req_0) ##1 state==IDLE ##1 state==GNT0);

endmodule

// Bind into DUT
bind fsm_using_single_always
  fsm_using_single_always_sva #(.SIZE(SIZE), .IDLE(IDLE), .GNT0(GNT0), .GNT1(GNT1))
  u_fsm_using_single_always_sva (
    .clock(clock),
    .reset(reset),
    .req_0(req_0),
    .req_1(req_1),
    .gnt_0(gnt_0),
    .gnt_1(gnt_1),
    .state(state)
  );