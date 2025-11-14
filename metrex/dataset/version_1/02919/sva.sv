// SVA checker for traffic_controller
// Bind this checker to the DUT to verify behavior and provide coverage.

module traffic_controller_sva #(
  parameter int GREEN_TIME     = 10,
  parameter int YELLOW_TIME    = 2,
  parameter int RED_TIME       = 8,
  parameter int CROSSING_TIME  = 15
)(
  input  logic        clk,
  input  logic        reset,
  input  logic        pedestrian_button,
  input  logic [1:0]  traffic_light,
  input  logic        pedestrian_crossing,
  input  logic [3:0]  state,
  input  logic [3:0]  counter
);

  // State encodings (mirror DUT)
  localparam logic [3:0] S_G   = 4'b0100; // green
  localparam logic [3:0] S_Y   = 4'b0010; // yellow
  localparam logic [3:0] S_R   = 4'b1000; // red
  localparam logic [3:0] S_G2  = 4'b0101; // green other lane
  localparam logic [3:0] S_Y2  = 4'b0011; // yellow other lane
  localparam logic [3:0] S_PC  = 4'b1001; // pedestrian crossing

  localparam int T_G  = GREEN_TIME;
  localparam int T_Y  = YELLOW_TIME;
  localparam int T_R  = RED_TIME;
  localparam int T_PC = CROSSING_TIME;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Parameter fit checks (counter is 4 bits)
  initial begin
    assert (GREEN_TIME     <= 15) else $error("GREEN_TIME exceeds counter width");
    assert (YELLOW_TIME    <= 15) else $error("YELLOW_TIME exceeds counter width");
    assert (RED_TIME       <= 15) else $error("RED_TIME exceeds counter width");
    assert (CROSSING_TIME  <= 15) else $error("CROSSING_TIME exceeds counter width");
  end

  // Async reset drives state/counter immediately
  assert property (@(posedge clk) reset |-> (state==S_G && counter==0));

  // Legal state space only
  assert property (state inside {S_G,S_Y,S_R,S_G2,S_Y2,S_PC});

  // No X/Z on key signals (outside reset)
  assert property (!$isunknown({state,counter,traffic_light,pedestrian_crossing}));

  // Output mapping sanity
  assert property (state inside {S_G,S_PC} |-> traffic_light==2'b10);
  assert property (state inside {S_Y,S_Y2} |-> traffic_light==2'b01);
  assert property (state inside {S_R,S_G2} |-> traffic_light==2'b00);

  // No invalid light encoding
  assert property (traffic_light != 2'b11);

  // Pedestrian crossing reflects state exactly
  assert property (pedestrian_crossing == (state==S_PC));

  // Counter is within per-state bounds
  assert property (state==S_G  |-> counter <= T_G);
  assert property (state==S_Y  |-> counter <= T_Y);
  assert property (state==S_R  |-> counter <= T_R);
  assert property (state==S_G2 |-> counter <= T_G);
  assert property (state==S_Y2 |-> counter <= T_Y);
  assert property (state==S_PC |-> counter <= T_PC);

  // Counter resets on any state change
  assert property (state != $past(state) |-> counter==0);

  // Counter increments while staying in same state (and not taking a transition)
  assert property (state==S_G  && $past(state)==S_G  && $past(counter)!=T_G          |-> counter==$past(counter)+1);
  assert property (state==S_Y  && $past(state)==S_Y  && $past(counter)!=T_Y          |-> counter==$past(counter)+1);
  assert property (state==S_R  && $past(state)==S_R  && $past(counter)!=T_R && !$past(pedestrian_button) |-> counter==$past(counter)+1);
  assert property (state==S_G2 && $past(state)==S_G2 && $past(counter)!=T_G          |-> counter==$past(counter)+1);
  assert property (state==S_Y2 && $past(state)==S_Y2 && $past(counter)!=T_Y          |-> counter==$past(counter)+1);
  assert property (state==S_PC && $past(state)==S_PC && $past(counter)!=T_PC         |-> counter==$past(counter)+1);

  // Required transitions at terminal counts
  assert property ($past(state)==S_G  && $past(counter)==T_G  |-> state==S_Y  && counter==0);
  assert property ($past(state)==S_Y  && $past(counter)==T_Y  |-> state==S_R  && counter==0);
  assert property ($past(state)==S_R  && $past(counter)==T_R  |-> state==S_G2 && counter==0);
  assert property ($past(state)==S_G2 && $past(counter)==T_G  |-> state==S_Y2 && counter==0);
  assert property ($past(state)==S_Y2 && $past(counter)==T_Y  |-> state==S_R  && counter==0);
  assert property ($past(state)==S_PC && $past(counter)==T_PC |-> state==S_R  && counter==0);

  // Pedestrian button only takes effect in RED before terminal count
  assert property ($past(state)==S_R && $past(counter)!=T_R && $past(pedestrian_button) |-> state==S_PC && counter==0);

  // In RED, absent button and before terminal count, stay in RED
  assert property ($past(state)==S_R && $past(counter)!=T_R && !$past(pedestrian_button) |-> state==S_R);

  // Coverage: visit all states
  cover property (state==S_G);
  cover property (state==S_Y);
  cover property (state==S_R);
  cover property (state==S_G2);
  cover property (state==S_Y2);
  cover property (state==S_PC);

  // Coverage: main loop without pedestrian
  cover property (state==S_G ##1 state==S_Y ##1 state==S_R ##1 state==S_G2 ##1 state==S_Y2 ##1 state==S_R);

  // Coverage: pedestrian sequence from RED
  cover property ($past(state)==S_R && $rose(pedestrian_button) && $past(counter)!=T_R ##1 state==S_PC ##[1:$] state==S_R);

  // Coverage: exact dwell in GREEN followed by YELLOW
  cover property ((state==S_G && counter==0)
                  ##[1:$] (state==S_G && counter==T_G)
                  ##1 (state==S_Y && counter==0));

  // Coverage: exact dwell in PED crossing
  cover property ((state==S_PC && counter==0)
                  ##[1:$] (state==S_PC && counter==T_PC)
                  ##1 (state==S_R && counter==0));

endmodule

// Bind the SVA to all instances of traffic_controller
bind traffic_controller traffic_controller_sva #(
  .GREEN_TIME(GREEN_TIME),
  .YELLOW_TIME(YELLOW_TIME),
  .RED_TIME(RED_TIME),
  .CROSSING_TIME(CROSSING_TIME)
) u_traffic_controller_sva (
  .clk(clk),
  .reset(reset),
  .pedestrian_button(pedestrian_button),
  .traffic_light(traffic_light),
  .pedestrian_crossing(pedestrian_crossing),
  .state(state),
  .counter(counter)
);