// SVA checker for pipelined_edge_detect
// Bind this checker to the DUT to verify functionality and provide coverage.

module pipelined_edge_detect_checker (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        a,
  input  logic        delay,
  input  logic        rise,
  input  logic        fall,
  input  logic [1:0]  state,
  input  logic        a_delayed,
  input  logic        a_delayed2
);
  localparam logic [1:0] IDLE = 2'b00;
  localparam logic [1:0] RISE_DETECT = 2'b01;
  localparam logic [1:0] FALL_DETECT = 2'b10;

  // Reset behavior (asynchronous assert, sampled on clk)
  assert property (@(posedge clk)
    !rst_n |-> (state==IDLE && a_delayed==1'b0 && a_delayed2==1'b0 && rise==1'b0 && fall==1'b0));

  // State encoding safety
  assert property (@(posedge clk) disable iff (!rst_n)
    state inside {IDLE,RISE_DETECT,FALL_DETECT});

  // Pipeline register behavior
  assert property (@(posedge clk)
    rst_n && $past(rst_n) |-> a_delayed == $past(a));

  assert property (@(posedge clk)
    rst_n && $past(rst_n) |-> a_delayed2 == $past(a_delayed));

  // Mutual exclusion of outputs
  assert property (@(posedge clk) disable iff (!rst_n) !(rise && fall));

  // Outputs imply state and input-pattern consistency
  assert property (@(posedge clk) disable iff (!rst_n)
    rise |-> state==RISE_DETECT && !fall);

  assert property (@(posedge clk) disable iff (!rst_n)
    fall |-> state==FALL_DETECT && !rise);

  assert property (@(posedge clk)
    rst_n && $past(rst_n) && rise |-> ($past(a_delayed2)==1'b0 && $past(a_delayed)==1'b1));

  assert property (@(posedge clk)
    rst_n && $past(rst_n) && fall |-> ($past(a_delayed2)==1'b1 && $past(a_delayed)==1'b0));

  // Single-cycle pulse width on outputs
  assert property (@(posedge clk) disable iff (!rst_n) rise |=> !rise);
  assert property (@(posedge clk) disable iff (!rst_n) fall |=> !fall);

  // External input-to-output timing relation (1-cycle latency)
  assert property (@(posedge clk) disable iff (!rst_n) $rose(a) |=> rise);
  assert property (@(posedge clk) disable iff (!rst_n) $fell(a) |=> fall);

  // Full state transition/function table checks (next-cycle behavior)
  // From IDLE
  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==IDLE && $past(a_delayed2)==1'b0 && $past(a_delayed)==1'b1
    |-> state==RISE_DETECT && rise && !fall);

  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==IDLE && $past(a_delayed2)==1'b1 && $past(a_delayed)==1'b0
    |-> state==FALL_DETECT && !rise && fall);

  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==IDLE &&
    !($past(a_delayed2)==1'b0 && $past(a_delayed)==1'b1) &&
    !($past(a_delayed2)==1'b1 && $past(a_delayed)==1'b0)
    |-> state==IDLE && !rise && !fall);

  // From RISE_DETECT
  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==RISE_DETECT && $past(a_delayed2)==1'b1 && $past(a_delayed)==1'b1
    |-> state==IDLE && !rise && !fall);

  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==RISE_DETECT && $past(a_delayed2)==1'b0 && $past(a_delayed)==1'b1
    |-> state==RISE_DETECT && rise && !fall);

  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==RISE_DETECT &&
    !($past(a_delayed2)==1'b1 && $past(a_delayed)==1'b1) &&
    !($past(a_delayed2)==1'b0 && $past(a_delayed)==1'b1)
    |-> state==IDLE && !rise && !fall);

  // From FALL_DETECT
  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==FALL_DETECT && $past(a_delayed2)==1'b0 && $past(a_delayed)==1'b0
    |-> state==IDLE && !rise && !fall);

  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==FALL_DETECT && $past(a_delayed2)==1'b1 && $past(a_delayed)==1'b0
    |-> state==FALL_DETECT && !rise && fall);

  assert property (@(posedge clk)
    rst_n && $past(rst_n) &&
    $past(state)==FALL_DETECT &&
    !($past(a_delayed2)==1'b0 && $past(a_delayed)==1'b0) &&
    !($past(a_delayed2)==1'b1 && $past(a_delayed)==1'b0)
    |-> state==IDLE && !rise && !fall);

  // Coverage
  cover property (@(posedge clk) disable iff (!rst_n) rise);
  cover property (@(posedge clk) disable iff (!rst_n) fall);
  cover property (@(posedge clk) disable iff (!rst_n) state==RISE_DETECT);
  cover property (@(posedge clk) disable iff (!rst_n) state==FALL_DETECT);
  cover property (@(posedge clk) disable iff (!rst_n) $rose(a) ##1 rise ##1 $fell(a) ##1 fall);
  cover property (@(posedge clk) disable iff (!rst_n) $fell(a) ##1 fall ##1 $rose(a) ##1 rise);

endmodule

// Bind to DUT
bind pipelined_edge_detect pipelined_edge_detect_checker u_pipelined_edge_detect_checker (
  .clk(clk),
  .rst_n(rst_n),
  .a(a),
  .delay(delay),
  .rise(rise),
  .fall(fall),
  .state(state),
  .a_delayed(a_delayed),
  .a_delayed2(a_delayed2)
);