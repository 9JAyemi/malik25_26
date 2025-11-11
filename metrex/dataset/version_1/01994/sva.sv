// SVA checker for traffic_light_controller
module traffic_light_controller_sva (
  input logic clk,
  input logic areset,
  input logic pedestrian_button,
  input logic red_light,
  input logic yellow_light,
  input logic green_light,
  input logic walk_signal
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (areset);

  // State encodings by observable outputs
  let S0 =  red_light && !yellow_light && !green_light && !walk_signal; // R, no walk
  let S1 =  red_light && !yellow_light && !green_light &&  walk_signal; // R, walk
  let S2 = !red_light &&  yellow_light && !green_light && !walk_signal; // Y, no walk
  let S3 = !red_light && !yellow_light &&  green_light &&  walk_signal; // G, walk
  let S4 = !red_light &&  yellow_light && !green_light &&  walk_signal; // Y, walk

  // Basic signal sanity
  assert property (!$isunknown({red_light, yellow_light, green_light, walk_signal})))
    else $error("Traffic light outputs contain X/Z");
  assert property ($onehot({red_light, yellow_light, green_light}))
    else $error("Exactly one of red/yellow/green must be 1");
  assert property (S0 || S1 || S2 || S3 || S4)
    else $error("Outputs not matching any valid state pattern");

  // Reset behavior: next cycle after reset assertion must be S0
  property rst_to_S0;
    @(posedge clk) areset |=> S0;
  endproperty
  assert property (rst_to_S0)
    else $error("Did not go to S0 after reset");

  // Input known when used for branching
  assert property (S0 |-> !$isunknown(pedestrian_button))
    else $error("pedestrian_button X/Z when needed in S0");

  // Legal transitions
  assert property (S0 &&  pedestrian_button |=> S4)
    else $error("S0 + ped -> must go to S4");
  assert property (S0 && !pedestrian_button |=> S1)
    else $error("S0 + no ped -> must go to S1");
  assert property (S0 |=> (S1 || S4))
    else $error("S0 must go to S1 or S4");

  assert property (S1 |=> S2) else $error("S1 must go to S2");
  assert property (S2 |=> S3) else $error("S2 must go to S3");
  assert property (S3 |=> S0) else $error("S3 must go to S0");
  assert property (S4 |=> S0) else $error("S4 must go to S0");

  // Coverage: hit all states and all transitions, both branches from S0
  cover property (S0);
  cover property (S1);
  cover property (S2);
  cover property (S3);
  cover property (S4);

  cover property (S0 && !pedestrian_button ##1 S1);
  cover property (S1 ##1 S2);
  cover property (S2 ##1 S3);
  cover property (S3 ##1 S0);
  cover property (S0 && pedestrian_button ##1 S4);
  cover property (S4 ##1 S0);

  // Full cycles
  cover property (S0 && !pedestrian_button ##1 S1 ##1 S2 ##1 S3 ##1 S0);
  cover property (S0 &&  pedestrian_button ##1 S4 ##1 S0);

  // Reset coverage
  cover property (@(posedge clk) areset ##1 S0);

endmodule

// Bind into DUT (example)
// bind traffic_light_controller traffic_light_controller_sva sva (.*);