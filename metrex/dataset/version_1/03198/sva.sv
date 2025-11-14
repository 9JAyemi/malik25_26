module traffic_light_control_sva #(
  parameter int GREEN_TIME  = 30,
  parameter int YELLOW_TIME = 5,
  parameter int RED_TIME    = 25
) (
  input  logic       clk,
  input  logic       reset,
  input  logic       red,
  input  logic       yellow,
  input  logic       green,
  input  logic [3:0] state,
  input  logic [5:0] counter
);

  localparam int GT = GREEN_TIME*2;
  localparam int YT = YELLOW_TIME*2;
  localparam int RT = RED_TIME*2;

  default clocking cb @(posedge clk); endclocking

  // Reset effect (checked even during reset)
  assert property (reset |=> state==4'b0001 && counter==0);

  // All other checks disabled during reset
  default disable iff (reset);

  // State encoding valid and one-hot across bits [2:0]; MSB stuck at 0
  assert property (state[3]==1'b0 && $onehot(state[2:0]));

  // Outputs exactly reflect state bits (and are one-hot)
  assert property ({red,yellow,green} == state[2:0]);

  // No X/Z on key signals after reset
  assert property (!$isunknown({state, counter, red, yellow, green}));

  // Counter bounds per state
  assert property ((state==4'b0001) |-> counter <= GT);
  assert property ((state==4'b0010) |-> counter <= YT);
  assert property ((state==4'b0100) |-> counter <= RT);

  // Hold state and increment counter while below limit
  assert property ((state==4'b0001 && counter<GT) |=> state==4'b0001 && counter==$past(counter)+1);
  assert property ((state==4'b0010 && counter<YT) |=> state==4'b0010 && counter==$past(counter)+1);
  assert property ((state==4'b0100 && counter<RT) |=> state==4'b0100 && counter==$past(counter)+1);

  // Transition exactly at limit with counter reset
  assert property ((state==4'b0001 && counter==GT) |=> state==4'b0010 && counter==0);
  assert property ((state==4'b0010 && counter==YT) |=> state==4'b0100 && counter==0);
  assert property ((state==4'b0100 && counter==RT) |=> state==4'b0001 && counter==0);

  // Any state change implies counter reload to 0
  assert property ((state != $past(state)) |-> counter==0);

  // Coverage: full cycle Green -> Yellow -> Red -> Green, with proper reloads
  cover property (state==4'b0001 && counter==0
                  ##1 (state==4'b0010 && counter==0)
                  ##1 (state==4'b0100 && counter==0)
                  ##1 (state==4'b0001 && counter==0));
endmodule

bind traffic_light_control traffic_light_control_sva #(
  .GREEN_TIME(GREEN_TIME),
  .YELLOW_TIME(YELLOW_TIME),
  .RED_TIME(RED_TIME)
) tlight_sva (
  .clk(clk),
  .reset(reset),
  .red(red),
  .yellow(yellow),
  .green(green),
  .state(state),
  .counter(counter)
);