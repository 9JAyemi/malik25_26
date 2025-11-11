// SystemVerilog Assertions for traffic_light
// Bind these into the DUT; concise but covers state/output/counter behavior and key corner cases.

module traffic_light_sva (input logic clk, reset);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Sanity
  assert property (!$isunknown({state, red_light, yellow_light, green_light, pedestrian_light,
                                red_counter, yellow_counter, green_counter, pedestrian_counter}));
  assert property (state inside {IDLE, TRAFFIC_LIGHT, PEDESTRIAN_LIGHT});

  // Outputs vs state
  assert property (state==IDLE            |->  red_light && !yellow_light && !green_light && !pedestrian_light);
  assert property (state==TRAFFIC_LIGHT   |-> !red_light &&  yellow_light && !green_light && !pedestrian_light);
  assert property (state==PEDESTRIAN_LIGHT|->  red_light && !yellow_light && !green_light &&  pedestrian_light);
  assert property ($onehot0({red_light,yellow_light,green_light}));
  assert property (pedestrian_light |-> state==PEDESTRIAN_LIGHT);
  assert property (state==$past(state) |-> $stable({red_light,yellow_light,green_light,pedestrian_light}));

  // IDLE state timing and transitions (pedestrian override wins)
  assert property ($past(state)==IDLE && $past(pedestrian_button)
                   |-> state==PEDESTRIAN_LIGHT); // override even if red_counter==5
  assert property ($past(state)==IDLE && !$past(pedestrian_button) && $past(red_counter)!=5
                   |-> state==IDLE && red_counter==$past(red_counter)+1);
  assert property ($past(state)==IDLE && !$past(pedestrian_button) && $past(red_counter)==5
                   |-> state==TRAFFIC_LIGHT && red_counter==0);
  assert property (state!=IDLE |-> $stable(red_counter));

  // TRAFFIC_LIGHT timing and transitions
  assert property ($past(state)==TRAFFIC_LIGHT && $past(yellow_counter)!=2
                   |-> state==TRAFFIC_LIGHT && yellow_counter==$past(yellow_counter)+1);
  assert property ($past(state)==TRAFFIC_LIGHT && $past(yellow_counter)==2
                   |-> state==PEDESTRIAN_LIGHT && yellow_counter==0);
  assert property (state!=TRAFFIC_LIGHT |-> $stable(yellow_counter));

  // PEDESTRIAN_LIGHT timing and transitions
  assert property ($past(state)==PEDESTRIAN_LIGHT && $past(pedestrian_counter)!=5
                   |-> state==PEDESTRIAN_LIGHT && pedestrian_counter==$past(pedestrian_counter)+1);
  assert property ($past(state)==PEDESTRIAN_LIGHT && $past(pedestrian_counter)==5
                   |-> state==IDLE && pedestrian_counter==0);
  assert property (state!=PEDESTRIAN_LIGHT |-> $stable(pedestrian_counter));

  // Unused/forbidden
  assert property (green_light==0);        // green never asserted in this RTL
  assert property ($stable(green_counter)); // never used/changed

  // No illegal jumps
  assert property ($past(state)==TRAFFIC_LIGHT   |-> state inside {TRAFFIC_LIGHT, PEDESTRIAN_LIGHT});
  assert property ($past(state)==PEDESTRIAN_LIGHT|-> state inside {PEDESTRIAN_LIGHT, IDLE});

  // Coverage
  cover property (state==IDLE ##1 state==TRAFFIC_LIGHT ##1 state==PEDESTRIAN_LIGHT ##1 state==IDLE);
  cover property ($past(state)==IDLE && $past(pedestrian_button) ##1 state==PEDESTRIAN_LIGHT);
  cover property ($past(state)==IDLE && $past(red_counter)==5 && $past(pedestrian_button) ##1 state==PEDESTRIAN_LIGHT);
  cover property (green_light); // should remain uncovered
endmodule

bind traffic_light traffic_light_sva u_traffic_light_sva (.clk(clk), .reset(reset));