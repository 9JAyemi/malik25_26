// SystemVerilog Assertions for traffic_light_controller
// Concise, high-quality checks + key coverage

module traffic_light_controller_sva (
  input  logic        clk,
  input  logic        pedestrian_button,
  input  logic        red_light,
  input  logic        yellow_light,
  input  logic        green_light,
  input  logic [5:0]  counter,
  input  logic [3:0]  pedestrian_counter
);
  default clocking cb @(posedge clk); endclocking

  // Make $past() safe
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Basic invariants
  assert property (!$isunknown({red_light, yellow_light, green_light}));
  assert property ($onehot0({red_light, yellow_light, green_light}));

  // Pedestrian mode forces all lights off
  assert property (pedestrian_button |-> !red_light && !yellow_light && !green_light);

  // Counter progresses: +1 each cycle, except reset to 0 when in normal mode and old counter >= 45
  assert property (counter == ((!pedestrian_button && $past(counter) >= 6'd45) ? 6'd0
                                                                             : ($past(counter) + 6'd1)));

  // Pedestrian counter behavior
  assert property ( pedestrian_button && ($past(pedestrian_counter) <  4'd10)
                    |-> pedestrian_counter == $past(pedestrian_counter) + 4'd1 );
  assert property ( pedestrian_button && ($past(pedestrian_counter) >= 4'd10)
                    |-> pedestrian_counter == 4'd0 );
  assert property ( !pedestrian_button |-> pedestrian_counter == $past(pedestrian_counter) );

  // Normal-mode lights mapping (exclude the single hazard cycle when exiting ped mode at wrap)
  // Hazard if: current normal mode, previous cycle was ped mode, and previous counter >= 45
  assert property ( (!pedestrian_button && !($past(pedestrian_button) && $past(counter) >= 6'd45) && (counter < 6'd20))
                    |->  green_light && !yellow_light && !red_light );
  assert property ( (!pedestrian_button && !($past(pedestrian_button) && $past(counter) >= 6'd45) && (counter >= 6'd20 && counter < 6'd25))
                    |->  yellow_light && !green_light && !red_light );
  assert property ( (!pedestrian_button && !($past(pedestrian_button) && $past(counter) >= 6'd45) && (counter >= 6'd25 && counter < 6'd45))
                    |->  red_light && !yellow_light && !green_light );

  // Exiting pedestrian mode exactly at wrap: current cycle holds all-off, next normal cycle goes green
  assert property ( $fell(pedestrian_button) && $past(counter) >= 6'd45
                    |-> counter == 6'd0 && !red_light && !yellow_light && !green_light );
  assert property ( $fell(pedestrian_button) && $past(counter) >= 6'd45 ##1 !pedestrian_button
                    |-> green_light && !yellow_light && !red_light );

  // Staying in normal mode across wrap: become green on the next cycle
  assert property ( $past(!pedestrian_button && counter >= 6'd45) && !pedestrian_button
                    |-> ##1 green_light );

  // Coverage
  // 1) Full normal sequence: green -> yellow -> red -> green (pedestrian_button stays low)
  cover property ( !pedestrian_button && green_light
                   ##[1:$] (!pedestrian_button && yellow_light)
                   ##[1:$] (!pedestrian_button && red_light)
                   ##[1:$] (!pedestrian_button && green_light) );

  // 2) Pedestrian mode sustained long enough to hit the internal reset behavior
  cover property ( pedestrian_button [*12] );

  // 3) Exit pedestrian at wrap and resume green next cycle
  cover property ( $fell(pedestrian_button) && $past(counter) >= 6'd45
                   ##1 (!pedestrian_button && green_light) );
endmodule

bind traffic_light_controller traffic_light_controller_sva u_traffic_light_controller_sva (
  .clk                 (clk),
  .pedestrian_button   (pedestrian_button),
  .red_light           (red_light),
  .yellow_light        (yellow_light),
  .green_light         (green_light),
  .counter             (counter),
  .pedestrian_counter  (pedestrian_counter)
);