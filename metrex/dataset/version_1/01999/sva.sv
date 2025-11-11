// SVA checker bound into KeyScanController
module KeyScanController_sva #(parameter int DIVIDER = 3);
  localparam int MAX = DIVIDER-1;

  default clocking cb @(posedge clk); endclocking

  // Async reset values observed on next clk
  assert property (@(posedge clk) rst |-> (currentState==3'b000 && startTimer==0 && timer==0));

  default disable iff (rst);

  // Sanity and encoding
  assert property (!$isunknown({currentState,startTimer,timer}));
  assert property (currentState inside {3'b000,3'b001,3'b010,3'b100});

  // State 000 (idle)
  assert property (currentState==3'b000 |-> timer==0);
  assert property (currentState==3'b000 && !start |=> currentState==3'b000 && startTimer==0 && timer==0);
  assert property (currentState==3'b000 && start |-> startTimer);
  assert property (currentState==3'b000 && start |=> currentState==3'b001 && startTimer==0 && timer==0);

  // State 001 (decision delay)
  assert property (currentState==3'b001 && timer < MAX |=> currentState==3'b001 && timer==$past(timer)+1 && startTimer==0);
  assert property (currentState==3'b001 && timer==MAX && load |=> currentState==3'b010 && timer==0);
  assert property (currentState==3'b001 && timer==MAX && !load && shift |=> currentState==3'b100 && timer==0);
  assert property (currentState==3'b001 && timer==MAX && !load && !shift |=> currentState==3'b000 && timer==0);
  // Priority when both load and shift
  assert property (currentState==3'b001 && timer==MAX && load && shift |=> currentState==3'b010);

  // State 010 (load delay)
  assert property (currentState==3'b010 && timer < MAX |=> currentState==3'b010 && timer==$past(timer)+1);
  assert property (currentState==3'b010 && timer==MAX |=> currentState==3'b001 && timer==0);

  // State 100 (shift delay)
  assert property (currentState==3'b100 && timer < MAX |=> currentState==3'b100 && timer==$past(timer)+1);
  assert property (currentState==3'b100 && timer==MAX |=> currentState==3'b001 && timer==0);

  // Timer never exceeds MAX
  assert property (timer <= MAX);

  // Functional coverage
  cover property (currentState==3'b000 && start ##1 currentState==3'b001);
  cover property (currentState==3'b001 && timer==MAX && load ##1 currentState==3'b010 ##[1:MAX] currentState==3'b001);
  cover property (currentState==3'b001 && timer==MAX && !load && shift ##1 currentState==3'b100 ##[1:MAX] currentState==3'b001);
  cover property (currentState==3'b001 && timer==MAX && !load && !shift ##1 currentState==3'b000);
  cover property (currentState==3'b001 && timer==MAX && load && shift ##1 currentState==3'b010);
  cover property (currentState==3'b010 ##[1:MAX] currentState==3'b001 ##[1:MAX] currentState==3'b100 ##[1:MAX] currentState==3'b001);
endmodule

bind KeyScanController KeyScanController_sva #(.DIVIDER(DIVIDER)) ks_sva();