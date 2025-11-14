// SVA for traffic_light
// Bind these assertions to the DUT. They check reset behavior, legal states,
// outputs per state, counter progression, legal transitions, and provide concise coverage.

module traffic_light_sva #(
  parameter int GREEN_TIME  = 500_000_000,
  parameter int YELLOW_TIME = 100_000_000,
  parameter int RED_TIME    = 500_000_000
)(
  input  logic        clk, reset, ped_cross,
  input  logic        green, yellow, red, ped_red, ped_green,
  input  logic [2:0]  state,
  input  logic [29:0] green_count, yellow_count, red_count,
  input  logic [29:0] ped_red_count, ped_green_count
);

  localparam logic [2:0]
    S_G   = 3'b001,
    S_Y   = 3'b010,
    S_R   = 3'b011,
    S_PR  = 3'b101,
    S_PG  = 3'b110,
    S_PR2 = 3'b111;

  default clocking cb @(posedge clk); endclocking
  // Use explicit reset checks where needed since reset is synchronous.

  // Synchronous reset puts FSM, counters, and outputs into known state
  assert property (cb reset |-> state==S_G
                            && green_count==0 && yellow_count==0 && red_count==0
                            && ped_red_count==0 && ped_green_count==0
                            && green && !yellow && !red && !ped_red && !ped_green);

  // State encoding must be legal
  assert property (cb state inside {S_G,S_Y,S_R,S_PR,S_PG,S_PR2});

  // Output correctness per state
  assert property (cb !reset && state==S_G  |-> green && !yellow && !red && !ped_red && !ped_green);
  assert property (cb !reset && state==S_Y  |-> !green &&  yellow && !red && !ped_red && !ped_green);
  assert property (cb !reset && state==S_R  |-> !green && !yellow &&  red && !ped_red && !ped_green);
  assert property (cb !reset && state==S_PR |-> !green && !yellow && !red &&  ped_red && !ped_green);
  assert property (cb !reset && state==S_PG |-> !green && !yellow && !red && !ped_red &&  ped_green);
  assert property (cb !reset && state==S_PR2|-> !green && !yellow && !red &&  ped_red && !ped_green);

  // One-hot constraints
  assert property (cb !reset && (state inside {S_G,S_Y,S_R})  |-> $onehot({green,yellow,red}) && !ped_red && !ped_green);
  assert property (cb !reset && (state inside {S_PR,S_PG,S_PR2}) |-> !green && !yellow && !red && $onehot({ped_red,ped_green}));

  // Legal transitions only
  assert property (cb !reset && state==S_G  |=> (state==S_G)  || (state==S_Y));
  assert property (cb !reset && state==S_Y  |=> (state==S_Y)  || (state==S_R));
  assert property (cb !reset && state==S_R  |=> (state==S_R)  || (state==S_G) || (state==S_PR));
  assert property (cb !reset && state==S_PR |=> (state==S_PR) || (state==S_PG));
  assert property (cb !reset && state==S_PG |=> (state==S_PG) || (state==S_PR2));
  assert property (cb !reset && state==S_PR2|=> (state==S_PR2)|| (state==S_G));

  // Green state timing: increment until limit, then transition to Yellow with resets/outputs
  assert property (cb !reset && state==S_G && green_count < GREEN_TIME
                   |=> state==S_G && green_count == $past(green_count)+1
                                   && $stable(yellow_count) && $stable(red_count)
                                   && $stable(ped_red_count) && $stable(ped_green_count));
  assert property (cb !reset && state==S_G && green_count == GREEN_TIME
                   |=> state==S_Y && green_count==0 && yellow_count==0
                                   && !green && yellow);

  // Yellow state timing
  assert property (cb !reset && state==S_Y && yellow_count < YELLOW_TIME
                   |=> state==S_Y && yellow_count == $past(yellow_count)+1
                                   && $stable(green_count) && $stable(red_count)
                                   && $stable(ped_red_count) && $stable(ped_green_count));
  assert property (cb !reset && state==S_Y && yellow_count == YELLOW_TIME
                   |=> state==S_R && yellow_count==0 && red_count==0
                                   && !yellow && red);

  // Red state timing and ped_cross handling (ped_cross has priority)
  assert property (cb !reset && state==S_R && ped_cross
                   |=> state==S_PR && ped_red && !red
                                    && ped_red_count==0 && red_count==0);
  assert property (cb !reset && state==S_R && !ped_cross && red_count < RED_TIME
                   |=> state==S_R && red_count == $past(red_count)+1
                                   && $stable(green_count) && $stable(yellow_count)
                                   && $stable(ped_red_count) && $stable(ped_green_count));
  assert property (cb !reset && state==S_R && !ped_cross && red_count == RED_TIME
                   |=> state==S_G && red_count==0 && green_count==0
                                   && !red && green);

  // Pedestrian red timing
  assert property (cb !reset && state==S_PR && ped_red_count < RED_TIME
                   |=> state==S_PR && ped_red_count == $past(ped_red_count)+1
                                    && $stable(green_count) && $stable(yellow_count)
                                    && $stable(red_count) && $stable(ped_green_count));
  assert property (cb !reset && state==S_PR && ped_red_count == RED_TIME
                   |=> state==S_PG && ped_red==0 && ped_green && ped_green_count==0);

  // Pedestrian green timing
  assert property (cb !reset && state==S_PG && ped_green_count < GREEN_TIME
                   |=> state==S_PG && ped_green_count == $past(ped_green_count)+1
                                    && $stable(green_count) && $stable(yellow_count)
                                    && $stable(red_count) && $stable(ped_red_count));
  assert property (cb !reset && state==S_PG && ped_green_count == GREEN_TIME
                   |=> state==S_PR2 && ped_green==0 && ped_red && ped_green_count==0);

  // Pedestrian red (return) timing
  assert property (cb !reset && state==S_PR2 && ped_red_count < RED_TIME
                   |=> state==S_PR2 && ped_red_count == $past(ped_red_count)+1
                                     && $stable(green_count) && $stable(yellow_count)
                                     && $stable(red_count) && $stable(ped_green_count));
  assert property (cb !reset && state==S_PR2 && ped_red_count == RED_TIME
                   |=> state==S_G && ped_red==0 && green && green_count==0 && ped_red_count==0);

  // Coverage: hit all states and both main cycles
  cover property (cb !reset && state==S_G && green_count==GREEN_TIME ##1 state==S_Y);
  cover property (cb !reset && state==S_Y && yellow_count==YELLOW_TIME ##1 state==S_R);
  cover property (cb !reset && state==S_R && !ped_cross && red_count==RED_TIME ##1 state==S_G);

  // Coverage: pedestrian cycle from red on ped_cross
  cover property (cb !reset && state==S_R && ped_cross ##1 state==S_PR
                               ##[1:$] state==S_PG
                               ##[1:$] state==S_PR2
                               ##[1:$] state==S_G);
endmodule

// Bind example (connect to internals). Adjust instance path if needed.
bind traffic_light traffic_light_sva #(
  .GREEN_TIME(GREEN_TIME), .YELLOW_TIME(YELLOW_TIME), .RED_TIME(RED_TIME)
) u_traffic_light_sva (
  .clk(clk), .reset(reset), .ped_cross(ped_cross),
  .green(green), .yellow(yellow), .red(red), .ped_red(ped_red), .ped_green(ped_green),
  .state(state),
  .green_count(green_count), .yellow_count(yellow_count), .red_count(red_count),
  .ped_red_count(ped_red_count), .ped_green_count(ped_green_count)
);