// SVA for traffic_light_fsm
// Bind this file to the DUT
module traffic_light_fsm_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        NSG_LED,
  input  logic        EWG_LED,
  input  logic        yellow_LED,
  input  logic [1:0]  state_reg,
  input  logic [5:0]  count
);
  localparam logic [1:0] NSG         = 2'b00;
  localparam logic [1:0] NSG_YELLOW  = 2'b01;
  localparam logic [1:0] EWG         = 2'b10;
  localparam logic [1:0] EWG_YELLOW  = 2'b11;

  localparam int NSG_DUR  = 30;
  localparam int NSGY_DUR = 5;
  localparam int EWG_DUR  = 20;
  localparam int EWGY_DUR = 5;

  default clocking cb @(posedge clk); endclocking

  // No X/Z on critical signals
  a_knowns: assert property ( !$isunknown({reset, state_reg, count, NSG_LED, EWG_LED, yellow_LED}) );

  // Reset behavior
  a_reset_state:   assert property ( reset |-> (state_reg==NSG) );
  a_reset_outputs: assert property ( reset |-> (NSG_LED && !EWG_LED && !yellow_LED) );
  a_reset_cnt_hold:assert property ( reset && $past(reset) |-> count==$past(count) );

  // Output decode must match state
  a_out_NSG:   assert property ( (state_reg==NSG)        |-> ( NSG_LED && !EWG_LED && !yellow_LED) );
  a_out_NSGY:  assert property ( (state_reg==NSG_YELLOW) |-> (!NSG_LED && !EWG_LED &&  yellow_LED) );
  a_out_EWG:   assert property ( (state_reg==EWG)        |-> (!NSG_LED &&  EWG_LED && !yellow_LED) );
  a_out_EWGY:  assert property ( (state_reg==EWG_YELLOW) |-> (!NSG_LED && !EWG_LED &&  yellow_LED) );

  // Per-state timing/transition rules (increment, hold, and exact transition)
  a_nsg_rules: assert property ( disable iff (reset)
    ((state_reg==NSG && count < NSG_DUR)  |=> (state_reg==NSG        && count==$past(count)+1))
    and
    ((state_reg==NSG && count==NSG_DUR)   |=> (state_reg==NSG_YELLOW && count==0))
  );

  a_nsgy_rules: assert property ( disable iff (reset)
    ((state_reg==NSG_YELLOW && count < NSGY_DUR) |=> (state_reg==NSG_YELLOW && count==$past(count)+1))
    and
    ((state_reg==NSG_YELLOW && count==NSGY_DUR)  |=> (state_reg==EWG       && count==0))
  );

  a_ewg_rules: assert property ( disable iff (reset)
    ((state_reg==EWG && count < EWG_DUR)  |=> (state_reg==EWG        && count==$past(count)+1))
    and
    ((state_reg==EWG && count==EWG_DUR)   |=> (state_reg==EWG_YELLOW && count==0))
  );

  a_ewgy_rules: assert property ( disable iff (reset)
    ((state_reg==EWG_YELLOW && count < EWGY_DUR) |=> (state_reg==EWG_YELLOW && count==$past(count)+1))
    and
    ((state_reg==EWG_YELLOW && count==EWGY_DUR)  |=> (state_reg==NSG        && count==0))
  );

  // Coverage
  c_seen_NSG:       cover property ( !reset && state_reg==NSG );
  c_seen_NSGY:      cover property ( !reset && state_reg==NSG_YELLOW );
  c_seen_EWG:       cover property ( !reset && state_reg==EWG );
  c_seen_EWGY:      cover property ( !reset && state_reg==EWG_YELLOW );

  c_full_cycle: cover property ( disable iff (reset)
    (state_reg==NSG && count==NSG_DUR) ##1
    (state_reg==NSG_YELLOW && count==0) ##[1:$]
    (state_reg==NSG_YELLOW && count==NSGY_DUR) ##1
    (state_reg==EWG && count==0) ##[1:$]
    (state_reg==EWG && count==EWG_DUR) ##1
    (state_reg==EWG_YELLOW && count==0) ##[1:$]
    (state_reg==EWG_YELLOW && count==EWGY_DUR) ##1
    (state_reg==NSG && count==0)
  );

  c_reset_seen: cover property ( reset );
endmodule

bind traffic_light_fsm traffic_light_fsm_sva sva (
  .clk(clk),
  .reset(reset),
  .NSG_LED(NSG_LED),
  .EWG_LED(EWG_LED),
  .yellow_LED(yellow_LED),
  .state_reg(state_reg),
  .count(count)
);