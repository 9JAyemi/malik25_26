// SVA for TrafficLightController
// Bind into the DUT to observe internal counter

module TrafficLightController_sva #(
  parameter int GREEN_TIME  = 20,
  parameter int YELLOW_TIME = 5,
  parameter int RED_TIME    = 15
)(
  input logic        clk,
  input logic        rst,
  input logic [1:0]  state,
  input logic [5:0]  counter
);

  localparam logic [1:0] G = 2'b01;
  localparam logic [1:0] Y = 2'b10;
  localparam logic [1:0] R = 2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Legal states only
  assert property (state inside {G,Y,R});

  // Asynchronous and synchronous reset behavior
  assert property (@(posedge rst) (state==G && counter==0));
  assert property (@(posedge clk) rst |-> (state==G && counter==0));

  // Counter bounds per state
  assert property ((state==G) |-> (counter <= GREEN_TIME));
  assert property ((state==Y) |-> (counter <= YELLOW_TIME));
  assert property ((state==R) |-> (counter <= RED_TIME));

  // Hold/increment when below threshold
  assert property (($past(state)==G && $past(counter) < GREEN_TIME)  |-> (state==G && counter==$past(counter)+1));
  assert property (($past(state)==Y && $past(counter) < YELLOW_TIME) |-> (state==Y && counter==$past(counter)+1));
  assert property (($past(state)==R && $past(counter) < RED_TIME)    |-> (state==R && counter==$past(counter)+1));

  // Transition exactly at threshold and counter resets
  assert property (($past(state)==G && $past(counter) >= GREEN_TIME)  |-> (state==Y && counter==0));
  assert property (($past(state)==Y && $past(counter) >= YELLOW_TIME) |-> (state==R && counter==0));
  assert property (($past(state)==R && $past(counter) >= RED_TIME)    |-> (state==G && counter==0));

  // Only allowed adjacency on any state change
  assert property ((state!=$past(state)) |-> (
                    ($past(state)==G && state==Y) ||
                    ($past(state)==Y && state==R) ||
                    ($past(state)==R && state==G)));

  // On any state entry, counter is 0
  assert property ((state!=$past(state)) |-> (counter==0));

  // Coverage
  cover property ((state==G) ##[1:$] (state==Y) ##[1:$] (state==R) ##[1:$] (state==G));
  cover property (($past(state)==G && $past(counter)==GREEN_TIME)  ##1 (state==Y && counter==0));
  cover property (($past(state)==Y && $past(counter)==YELLOW_TIME) ##1 (state==R && counter==0));
  cover property (($past(state)==R && $past(counter)==RED_TIME)    ##1 (state==G && counter==0));

endmodule

bind TrafficLightController TrafficLightController_sva #(
  .GREEN_TIME(20), .YELLOW_TIME(5), .RED_TIME(15)
) u_tlc_sva (.* , .counter(counter));