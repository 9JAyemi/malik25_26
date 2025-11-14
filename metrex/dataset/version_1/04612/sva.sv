// SVA for trafficLightController
package tlc_sva_pkg;
  localparam logic [1:0] S_RED    = 2'b00;
  localparam logic [1:0] S_GREEN  = 2'b10;
  localparam logic [1:0] S_YELLOW = 2'b01;

  localparam int D_RED   = 10;
  localparam int D_GREEN = 5;
  localparam int D_YELLOW= 2;
endpackage

import tlc_sva_pkg::*;

module tlc_assertions (
  input logic        clk,
  input logic [1:0]  currentState,
  input logic [1:0]  nextState,
  input logic [2:0]  count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({clk,currentState,nextState,count}));

  // Basic sanity
  assert property ( !$isunknown({currentState,nextState,count}) );
  assert property ( nextState inside {S_RED,S_GREEN,S_YELLOW} );

  // Power-on expectation (time 0)
  assert property ( $initstate |-> (nextState == S_RED) );

  // Default behavior on illegal state encoding
  assert property ( (currentState == 2'b11) |-> (nextState == S_RED) );

  // Dwell/transition rules
  // Red: count increments until 10, then transition to Green and reset count
  assert property ( (currentState==S_RED   && count < D_RED  ) |=> count == $past(count)+1 );
  assert property ( (currentState==S_RED   && count == D_RED ) |=> (nextState==S_GREEN && count==0) );

  // Green: count increments until 5, then transition to Yellow and reset count
  assert property ( (currentState==S_GREEN && count < D_GREEN) |=> count == $past(count)+1 );
  assert property ( (currentState==S_GREEN && count == D_GREEN) |=> (nextState==S_YELLOW && count==0) );

  // Yellow: count increments until 2, then transition to Red and reset count
  assert property ( (currentState==S_YELLOW&& count < D_YELLOW) |=> count == $past(count)+1 );
  assert property ( (currentState==S_YELLOW&& count == D_YELLOW) |=> (nextState==S_RED && count==0) );

  // Disallow illegal transition targets on threshold events
  assert property ( (currentState==S_RED   && count==D_RED)   |=> (nextState!=S_RED   && nextState!=S_YELLOW) );
  assert property ( (currentState==S_GREEN && count==D_GREEN) |=> (nextState!=S_GREEN && nextState!=S_RED)    );
  assert property ( (currentState==S_YELLOW&& count==D_YELLOW)|=> (nextState!=S_YELLOW&& nextState!=S_GREEN)  );

  // Coverage: each transition observed
  cover property ( (currentState==S_RED   && count==D_RED)   |=> (nextState==S_GREEN && count==0) );
  cover property ( (currentState==S_GREEN && count==D_GREEN) |=> (nextState==S_YELLOW&& count==0) );
  cover property ( (currentState==S_YELLOW&& count==D_YELLOW)|=> (nextState==S_RED   && count==0) );

  // Coverage: full R->G->Y->R cycle with required dwell counts
  cover property (
    (currentState==S_RED   && count==D_RED)   ##1 (nextState==S_GREEN && count==0) ##[1:$]
    (currentState==S_GREEN && count==D_GREEN) ##1 (nextState==S_YELLOW&& count==0) ##[1:$]
    (currentState==S_YELLOW&& count==D_YELLOW)##1 (nextState==S_RED   && count==0)
  );
endmodule

bind trafficLightController tlc_assertions u_tlc_assertions (
  .clk(clk),
  .currentState(currentState),
  .nextState(nextState),
  .count(count)
);