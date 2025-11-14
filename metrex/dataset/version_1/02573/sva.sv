// SVA for fsm_sequence_detection
// Bind into the DUT; focuses on correctness and concise full coverage.

module fsm_sequence_detection_sva;
  // Mirror encodings (kept local to avoid hierarchy dependencies)
  localparam S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11;

  // Default clock and reset
  default clocking cb @ (posedge clk); endclocking
  default disable iff (reset)

  // Shorthand
  let nibbleA = (data[7:4] == 4'hA);

  // Asynchronous reset effect and hold
  assert property (@(posedge reset) (state==S0 && match==1'b0));
  assert property (reset |-> (state==S0 && match==1'b0));

  // Clean (no X/Z) on state/match when not in reset
  assert property (!$isunknown({state,match}));

  // Next-state correctness (forward, complete)
  assert property ($past(state)==S0 &&  nibbleA |=> state==S1);
  assert property ($past(state)==S0 && !nibbleA |=> state==S0);

  assert property ($past(state)==S1 &&  nibbleA |=> state==S2);
  assert property ($past(state)==S1 && !nibbleA |=> state==S0);

  assert property ($past(state)==S2 &&  nibbleA |=> state==S3);
  assert property ($past(state)==S2 && !nibbleA |=> state==S0);

  assert property ($past(state)==S3 |=> state==S0);

  // match behavior: reflects prior state, pulses exactly 1 cycle
  assert property (match == ($past(state)==S3));
  assert property (match |=> !match);

  // Functional end-to-end coverage
  cover property ( (nibbleA)[*3] ##1 match );
  cover property ( state==S0 ##1 nibbleA ##1 state==S1
                   ##1 nibbleA ##1 state==S2
                   ##1 nibbleA ##1 state==S3
                   ##1 match ##1 state==S0 );
endmodule

bind fsm_sequence_detection fsm_sequence_detection_sva sva();