// SVA for traffic_light_fsm
module traffic_light_fsm_sva
  #(parameter logic [1:0] RED=2'b00, GREEN=2'b01, YELLOW=2'b10)
  (input  logic        clk, reset,
   input  logic        red, green, yellow,
   input  logic [1:0]  state, next_state,
   input  logic [3:0]  count);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // No X/Z on key signals (checked even during reset)
  assert property (@(posedge clk) !$isunknown({state,next_state,count,red,green,yellow}));

  // State legality
  assert property (state inside {RED,GREEN,YELLOW});
  assert property (next_state inside {RED,GREEN,YELLOW});

  // Outputs must be one-hot and decode state
  assert property ($onehot({red,green,yellow}));
  assert property ((state==RED)    |->  red && !green && !yellow);
  assert property ((state==GREEN)  |-> !red &&  green && !yellow);
  assert property ((state==YELLOW) |-> !red && !green &&  yellow);

  // Next-state combinational function
  assert property ((state==RED)    |-> next_state == ((count==5)  ? GREEN  : RED));
  assert property ((state==GREEN)  |-> next_state == ((count==10) ? YELLOW : GREEN));
  assert property ((state==YELLOW) |-> next_state == ((count==2)  ? RED    : YELLOW));

  // Registered update: state follows prior next_state
  assert property ($past(!reset) |-> state == $past(next_state));

  // Only legal registered transitions occur
  assert property ($past(!reset) && state != $past(state)
                   |-> (($past(state)==RED    && state==GREEN)  ||
                        ($past(state)==GREEN  && state==YELLOW) ||
                        ($past(state)==YELLOW && state==RED)));

  // Transitions happen only at the programmed counts
  assert property (($past(state)==RED    && state==GREEN)  |-> $past(count)==5);
  assert property (($past(state)==GREEN  && state==YELLOW) |-> $past(count)==10);
  assert property (($past(state)==YELLOW && state==RED)    |-> $past(count)==2);

  // Counter behavior
  assert property ($past(!reset) |-> count == $past(count) + 1);
  assert property (@(posedge clk) reset |-> (count==0 && state==RED && red && !green && !yellow));

  // Coverage
  cover property (state==RED);
  cover property (state==GREEN);
  cover property (state==YELLOW);

  cover property (($past(state)==RED    && state==GREEN  && $past(count)==5));
  cover property (($past(state)==GREEN  && state==YELLOW && $past(count)==10));
  cover property (($past(state)==YELLOW && state==RED    && $past(count)==2));

  cover property (
    ($past(state)==RED   && state==GREEN  && $past(count)==5) ##1
    ($past(state)==GREEN && state==YELLOW && $past(count)==10) ##1
    ($past(state)==YELLOW&& state==RED    && $past(count)==2)
  );

endmodule

bind traffic_light_fsm traffic_light_fsm_sva
  #(.RED(2'b00), .GREEN(2'b01), .YELLOW(2'b10))
  (.clk(clk), .reset(reset),
   .red(red), .green(green), .yellow(yellow),
   .state(state), .next_state(next_state), .count(count));