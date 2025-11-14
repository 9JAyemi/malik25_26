// SVA for fsm_traffic_light_control
module fsm_traffic_light_control_sva (
  input  logic        clock,
  input  logic        reset,
  input  logic        pedestrian_crossing_button,
  input  logic        green_light,
  input  logic        yellow_light,
  input  logic        red_light,
  input  logic [1:0]  state,
  input  logic [1:0]  next_state
);
  localparam logic [1:0] S0=2'b00, S1=2'b01, S2=2'b10, S3=2'b11;

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Sanity/knowns
  assert property (!$isunknown({state,next_state,green_light,yellow_light,red_light,pedestrian_crossing_button}));
  assert property (state inside {S0,S1,S2,S3});
  assert property (next_state inside {S0,S1,S2,S3});
  assert property ($onehot({green_light,yellow_light,red_light}));

  // Reset behavior (sync reset)
  assert property ($rose(reset) |=> state==S0);
  assert property (reset && $past(reset) |-> state==S0);

  // Output mapping (state -> lights)
  assert property ((state==S0) |-> (green_light && !yellow_light && !red_light));
  assert property ((state==S1) |-> (!green_light &&  yellow_light && !red_light));
  assert property ((state==S2) |-> (!green_light && !yellow_light &&  red_light));
  assert property ((state==S3) |-> (!green_light &&  yellow_light && !red_light));

  // Output implies state (no illegal light patterns)
  assert property (green_light  |-> state==S0);
  assert property (red_light    |-> state==S2);
  assert property (yellow_light |-> (state inside {S1,S3}));

  // Next-state combinational function correctness
  assert property ((state==S0 &&  pedestrian_crossing_button) |-> next_state==S1);
  assert property ((state==S0 && !pedestrian_crossing_button) |-> next_state==S0);
  assert property ((state==S1) |-> next_state==S2);
  assert property ((state==S2) |-> next_state==S3);
  assert property ((state==S3) |-> next_state==S0);

  // Registered state transitions
  assert property ((state==S0 &&  pedestrian_crossing_button) |=> state==S1);
  assert property ((state==S0 && !pedestrian_crossing_button) |=> state==S0);
  assert property ((state==S1) |=> state==S2);
  assert property ((state==S2) |=> state==S3);
  assert property ((state==S3) |=> state==S0);

  // Liveness timing: press -> red in 2 cycles, back to green in 4 cycles
  assert property ((state==S0 && pedestrian_crossing_button) |=> ##2 red_light);
  assert property ((state==S0 && pedestrian_crossing_button) |=> ##4 green_light);

  // Coverage
  cover property ((state==S0 && pedestrian_crossing_button) ##1 (state==S1) ##1 (state==S2) ##1 (state==S3) ##1 (state==S0));
  cover property ((state==S0 && !pedestrian_crossing_button)[*3] ##1 (state==S0 && pedestrian_crossing_button));
  cover property (green_light ##1 yellow_light ##1 red_light ##1 yellow_light ##1 green_light);
endmodule

bind fsm_traffic_light_control fsm_traffic_light_control_sva sva (
  .clock(clock),
  .reset(reset),
  .pedestrian_crossing_button(pedestrian_crossing_button),
  .green_light(green_light),
  .yellow_light(yellow_light),
  .red_light(red_light),
  .state(state),
  .next_state(next_state)
);