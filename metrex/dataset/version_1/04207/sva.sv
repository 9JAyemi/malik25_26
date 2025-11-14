// SVA for traffic_light_controller
// Bindable, parameterized to match DUT params and internal signals

module traffic_light_controller_sva #(
  parameter int P_ST_IDLE = 3'b000,
  parameter int P_ST_L1   = 3'b001,
  parameter int P_ST_L2   = 3'b010,
  parameter int P_ST_L3   = 3'b011,
  parameter int P_ST_R1   = 3'b100,
  parameter int P_ST_R2   = 3'b101,
  parameter int P_ST_R3   = 3'b110,
  parameter int P_DELAY   = 10
)(
  input  logic        clk,
  input  logic        reset,
  input  logic        left,
  input  logic        right,
  input  logic        LA, LB, LC,
  input  logic        RA, RB, RC,
  input  logic [2:0]  state,
  input  logic [2:0]  next_state,
  input  logic [3:0]  timer
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity
  assert property (state inside {P_ST_IDLE,P_ST_L1,P_ST_L2,P_ST_L3,P_ST_R1,P_ST_R2,P_ST_R3});
  assert property (next_state inside {P_ST_IDLE,P_ST_L1,P_ST_L2,P_ST_L3,P_ST_R1,P_ST_R2,P_ST_R3});

  // Reset behavior
  assert property (@(posedge clk) reset |-> (state==P_ST_IDLE && timer==0));

  // Registered state follows combinational next_state
  assert property (state == $past(next_state));

  // Global override: both turn signals force IDLE next_state
  assert property ((left && right) |-> (next_state == P_ST_IDLE));

  // IDLE transitions
  assert property ((state==P_ST_IDLE && left && !right) |-> next_state==P_ST_L1);
  assert property ((state==P_ST_IDLE && !left && right) |-> next_state==P_ST_R1);
  assert property ((state==P_ST_IDLE && !(left^right))  |-> next_state==P_ST_IDLE); // both 0 or both 1 -> IDLE

  // Left path
  assert property ((state==P_ST_L1) |-> next_state==P_ST_L2);

  assert property ((state==P_ST_L2 && (timer >= P_DELAY)) |-> next_state==P_ST_L3);
  assert property ((state==P_ST_L2 && (timer <  P_DELAY) && !(left && right)) |-> next_state==P_ST_L2);

  assert property ((state==P_ST_L3 &&  left && !right) |-> next_state==P_ST_L1);
  assert property ((state==P_ST_L3 && !left &&  right) |-> next_state==P_ST_R1);
  assert property ((state==P_ST_L3 && !(left^right) && (timer >= P_DELAY)) |-> next_state==P_ST_IDLE);
  assert property ((state==P_ST_L3 && !(left^right) && (timer <  P_DELAY)) |-> next_state==P_ST_L3);

  // Right path
  assert property ((state==P_ST_R1) |-> next_state==P_ST_R2);

  assert property ((state==P_ST_R2 && (timer >= P_DELAY)) |-> next_state==P_ST_R3);
  assert property ((state==P_ST_R2 && (timer <  P_DELAY) && !(left && right)) |-> next_state==P_ST_R2);

  assert property ((state==P_ST_R3 && !left &&  right) |-> next_state==P_ST_R1);
  assert property ((state==P_ST_R3 &&  left && !right) |-> next_state==P_ST_L1);
  assert property ((state==P_ST_R3 && !(left^right) && (timer >= P_DELAY)) |-> next_state==P_ST_IDLE);
  assert property ((state==P_ST_R3 && !(left^right) && (timer <  P_DELAY)) |-> next_state==P_ST_R3);

  // Timer behavior
  assert property ((state inside {P_ST_L2,P_ST_R2}) |-> timer == $past(timer)+1);
  assert property ((!(state inside {P_ST_L2,P_ST_R2})) |-> timer==0);

  // Output mapping correctness
  assert property ((state==P_ST_IDLE) |-> (!LA && !LB && !LC && !RA && !RB && !RC));

  assert property ((state==P_ST_L1) |-> ( LA && !LB && !LC && !RA && !RB && !RC));
  assert property ((state==P_ST_L2) |-> ( LA &&  LB && !LC && !RA && !RB && !RC));
  assert property ((state==P_ST_L3) |-> ( LA &&  LB &&  LC && !RA && !RB && !RC));

  assert property ((state==P_ST_R1) |-> (!LA && !LB && !LC &&  RA && !RB && !RC));
  assert property ((state==P_ST_R2) |-> (!LA && !LB && !LC &&  RA &&  RB && !RC));
  assert property ((state==P_ST_R3) |-> (!LA && !LB && !LC &&  RA &&  RB &&  RC));

  // Output invariants
  assert property (LC |-> (LB && LA));
  assert property (RC |-> (RB && RA));
  assert property (!((LA||LB||LC) && (RA||RB||RC))); // never light left and right simultaneously

  // Covers (reachability and key flows)
  cover property (state==P_ST_L1 ##1 state==P_ST_L2 ##1 state==P_ST_L3);
  cover property (state==P_ST_R1 ##1 state==P_ST_R2 ##1 state==P_ST_R3);
  cover property (state==P_ST_IDLE ##1 (left && !right) ##1 state==P_ST_L1 ##1 state==P_ST_L2 ##[1:$] state==P_ST_L3 ##[1:$] state==P_ST_IDLE);
  cover property (state==P_ST_IDLE ##1 (!left && right) ##1 state==P_ST_R1 ##1 state==P_ST_R2 ##[1:$] state==P_ST_R3 ##[1:$] state==P_ST_IDLE);
  cover property ((state==P_ST_L3 && !left && !right && timer>=P_DELAY) ##1 state==P_ST_IDLE);
  cover property ((state==P_ST_R3 && !left && !right && timer>=P_DELAY) ##1 state==P_ST_IDLE);
  cover property ((state inside {P_ST_L1,P_ST_L2,P_ST_L3,P_ST_R1,P_ST_R2,P_ST_R3}) && (left && right) ##1 state==P_ST_IDLE);

endmodule

// Bind into the DUT; connects internal regs by name.
// Adjust instance-targeting as needed; this binds to all instances of this module type.
bind traffic_light_controller traffic_light_controller_sva #(
  .P_ST_IDLE(traffic_light_controller.ST_IDLE),
  .P_ST_L1  (traffic_light_controller.ST_L1),
  .P_ST_L2  (traffic_light_controller.ST_L2),
  .P_ST_L3  (traffic_light_controller.ST_L3),
  .P_ST_R1  (traffic_light_controller.ST_R1),
  .P_ST_R2  (traffic_light_controller.ST_R2),
  .P_ST_R3  (traffic_light_controller.ST_R3),
  .P_DELAY  (traffic_light_controller.DELAY)
) traffic_light_controller_sva_i (
  .clk       (clk),
  .reset     (reset),
  .left      (left),
  .right     (right),
  .LA        (LA),
  .LB        (LB),
  .LC        (LC),
  .RA        (RA),
  .RB        (RB),
  .RC        (RC),
  .state     (state),
  .next_state(next_state),
  .timer     (timer)
);