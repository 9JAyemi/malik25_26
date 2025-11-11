// SVA checker for fsm_using_always
module fsm_using_always_sva #(
  parameter int SIZE = 3,
  parameter logic [SIZE-1:0] IDLE = 3'b001,
  parameter logic [SIZE-1:0] GNT0 = 3'b010,
  parameter logic [SIZE-1:0] GNT1 = 3'b100
)(
  input  logic                clock,
  input  logic                reset,
  input  logic                req_0,
  input  logic                req_1,
  input  logic                gnt_0,
  input  logic                gnt_1,
  input  logic [SIZE-1:0]     state
);

  // default SVA context
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Basic sanity
  ap_no_x_state:  assert property (!$isunknown(state));
  ap_no_x_grants: assert property (!$isunknown({gnt_0,gnt_1}));
  ap_grants_mutex: assert property (!(gnt_0 && gnt_1));

  // Legal encoding (one-hot and known states)
  ap_state_onehot: assert property ($onehot(state));
  ap_state_legal:  assert property (state inside {IDLE, GNT0, GNT1});

  // Next-state function (sequential semantics)
  ap_ns_idle: assert property (
    (state==IDLE) |=> (req_0 ? state==GNT0 :
                       req_1 ? state==GNT1 :
                               state==IDLE)
  );
  ap_ns_g0: assert property (
    (state==GNT0) |=> (req_0 ? state==GNT0 : state==IDLE)
  );
  ap_ns_g1: assert property (
    (state==GNT1) |=> (req_1 ? state==GNT1 : state==IDLE)
  );
  // Priority when both requests seen in IDLE
  ap_prio_both: assert property ((state==IDLE && req_0 && req_1) |=> state==GNT0);

  // Output mapping (registered one-cycle after state is observed)
  ap_out_idle: assert property ((state==IDLE) |=> (!gnt_0 && !gnt_1));
  ap_out_g0:   assert property ((state==GNT0) |=> ( gnt_0 && !gnt_1));
  ap_out_g1:   assert property ((state==GNT1) |=> (!gnt_0 &&  gnt_1));

  // Reset behavior (synchronous)
  ap_reset_init: assert property (@(posedge clock) reset |=> (state==IDLE && !gnt_0 && !gnt_1));

  // Safe recovery from illegal state (defensive)
  ap_illegal_recover: assert property (
    !(state inside {IDLE,GNT0,GNT1}) |=> (state==IDLE && !gnt_0 && !gnt_1)
  );

  // Functional coverage
  cp_reach_idle:  cover property (state==IDLE);
  cp_reach_g0:    cover property (state==GNT0);
  cp_reach_g1:    cover property (state==GNT1);
  cp_idle_to_g0:  cover property (state==IDLE && req_0      |=> state==GNT0);
  cp_idle_to_g1:  cover property (state==IDLE && !req_0 && req_1 |=> state==GNT1);
  cp_prio_both:   cover property (state==IDLE && req_0 && req_1  |=> state==GNT0);
  cp_g0_hold:     cover property (state==GNT0 && req_0 ##1 state==GNT0 && req_0);
  cp_g1_hold:     cover property (state==GNT1 && req_1 ##1 state==GNT1 && req_1);
  cp_release_g0:  cover property (state==GNT0 && !req_0 |=> state==IDLE);
  cp_release_g1:  cover property (state==GNT1 && !req_1 |=> state==IDLE);

endmodule

// Bind into DUT (connect internal state)
bind fsm_using_always fsm_using_always_sva #(
  .SIZE(SIZE), .IDLE(IDLE), .GNT0(GNT0), .GNT1(GNT1)
) fsm_using_always_sva_i (
  .clock(clock),
  .reset(reset),
  .req_0(req_0),
  .req_1(req_1),
  .gnt_0(gnt_0),
  .gnt_1(gnt_1),
  .state(state)
);