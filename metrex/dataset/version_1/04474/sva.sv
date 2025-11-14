// SVA checker for traffic_light_controller
module traffic_light_controller_sva #(
  parameter int G_DUR = 10,
  parameter int Y_DUR = 2,
  parameter int R_DUR = 10
)(
  input  logic       clk,
  input  logic       button,
  input  logic       red,
  input  logic       yellow,
  input  logic       green,
  input  logic [1:0] state,
  input  logic [3:0] counter
);

  localparam [1:0] STATE_GREEN  = 2'b00;
  localparam [1:0] STATE_YELLOW = 2'b01;
  localparam [1:0] STATE_RED    = 2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({button,state,counter,red,yellow,green}));

  // State encoding legal
  assert property (state inside {STATE_GREEN, STATE_YELLOW, STATE_RED});

  // Outputs are one-hot
  assert property ($onehot({red,yellow,green}));

  // Button forces sync reset to RED with counter=0
  assert property (button |=> (state==STATE_RED && counter==0));

  // Counter bounds per state (when not overridden by button)
  assert property (!button && state==STATE_GREEN  |-> counter <= G_DUR);
  assert property (!button && state==STATE_YELLOW |-> counter <= Y_DUR);
  assert property (!button && state==STATE_RED    |-> counter <= R_DUR);

  // GREEN behavior
  assert property (!button && state==STATE_GREEN && counter < G_DUR
                   |=> state==STATE_GREEN && counter==$past(counter)+1);
  assert property (!button && state==STATE_GREEN && counter == G_DUR
                   |=> state==STATE_YELLOW && counter==0);

  // YELLOW behavior
  assert property (!button && state==STATE_YELLOW && counter < Y_DUR
                   |=> state==STATE_YELLOW && counter==$past(counter)+1);
  assert property (!button && state==STATE_YELLOW && counter == Y_DUR
                   |=> state==STATE_RED && counter==0);

  // RED behavior
  assert property (!button && state==STATE_RED && counter < R_DUR
                   |=> state==STATE_RED && counter==$past(counter)+1);
  assert property (!button && state==STATE_RED && counter == R_DUR
                   |=> state==STATE_YELLOW && counter==0);

  // Outputs follow previous state (registered mapping)
  assert property (state==STATE_GREEN  |=>  green && !yellow && !red);
  assert property (state==STATE_YELLOW |=> !green &&  yellow && !red);
  assert property (state==STATE_RED    |=> !green && !yellow &&  red);

  // Coverage: states, transitions, and button override
  cover property (state==STATE_GREEN);
  cover property (state==STATE_YELLOW);
  cover property (state==STATE_RED);

  cover property (!button && state==STATE_GREEN  && counter==G_DUR ##1 state==STATE_YELLOW && counter==0);
  cover property (!button && state==STATE_YELLOW && counter==Y_DUR ##1 state==STATE_RED    && counter==0);
  cover property (!button && state==STATE_RED    && counter==R_DUR ##1 state==STATE_YELLOW && counter==0);

  cover property (button ##1 state==STATE_RED && counter==0);

endmodule

// Bind into DUT (accesses internal state/counter)
bind traffic_light_controller traffic_light_controller_sva #(
  .G_DUR(10), .Y_DUR(2), .R_DUR(10)
) u_tlc_sva (
  .clk(clk),
  .button(button),
  .red(red),
  .yellow(yellow),
  .green(green),
  .state(state),
  .counter(counter)
);