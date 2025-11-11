// SVA for fsm_traffic_light_control
// Bind into the DUT to observe internal signals
bind fsm_traffic_light_control fsm_traffic_light_control_sva svainst();

module fsm_traffic_light_control_sva;

  // Access DUT scope (clk, reset, state, next_state, counter, red/green/yellow, params)
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity
  assert property (!$isunknown({state,next_state,counter,red,green,yellow}));
  assert property (state inside {S0,S1,S2});

  // Combinational next_state logic must match spec
  assert property ((state==S0) |-> next_state==S1);
  assert property ((state==S1) |-> next_state==(counter==0 ? S2 : S1));
  assert property ((state==S2) |-> next_state==(counter==0 ? S0 : S2));

  // Sequential state update must follow next_state whenever previous cycle was not in reset
  assert property ($past(!reset) |-> state == $past(next_state));

  // Counter loads based on prior state/ped (NB semantics)
  assert property ($past(state)==S0 |-> counter==red_time);
  assert property ($past(state)==S1 &&  $past(ped) |-> counter==yellow_time);
  assert property ($past(state)==S1 && !$past(ped) |-> counter==green_time);
  assert property ($past(state)==S2 |-> counter==yellow_time);

  // Outputs reflect prior state/ped (NB semantics)
  assert property ($past(state)==S0 |-> red && !green && !yellow);
  assert property ($past(state)==S1 &&  $past(ped) |-> !red && !green &&  yellow);
  assert property ($past(state)==S1 && !$past(ped) |-> !red &&  green && !yellow);
  assert property ($past(state)==S2 |-> !red && !green &&  yellow);

  // Exactly one light on when not in reset
  assert property ($onehot({red,green,yellow}));

  // Reset behavior at clock edge
  assert property (@(posedge clk) reset |-> state==S0 && counter==0 && red && !green && !yellow);

  // Coverage
  cover property (state==S0);
  cover property (state==S1 && !ped);
  cover property (state==S1 &&  ped);
  cover property (state==S2);

  cover property ($past(state)==S0 && state==S1);                             // S0->S1
  cover property ($past(state)==S1 && $past(counter)==0 && state==S2);        // S1->S2 (intended)
  cover property ($past(state)==S2 && $past(counter)==0 && state==S0);        // S2->S0 (intended)

  cover property (red && !green && !yellow);
  cover property (!red && green && !yellow);
  cover property (!red && !green && yellow);

endmodule