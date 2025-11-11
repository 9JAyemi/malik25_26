// SVA for mealy_fsm_4bit_sequence_detection
// Bindable checker focusing on correctness and coverage of state transitions and match pulse

module mealy_fsm_4bit_sequence_detection_sva
  #(parameter logic [1:0] S0 = 2'b00,
                         S1 = 2'b01,
                         S2 = 2'b10)
(
  input  logic        clk,
  input  logic        reset,
  input  logic        data,
  input  logic        match,
  input  logic [1:0]  state
);

  default clocking @(posedge clk); endclocking
  // Disable functional checks during reset; use explicit reset properties where needed
  default disable iff (reset);

  // Basic sanity
  assert property (!$isunknown({state,match}))) else $error("X/Z detected on state/match");

  // Reset behavior (synchronous): on a reset cycle, next cycle must be clean
  assert property (@(posedge clk) reset |=> (state==S0 && match==1'b0))
    else $error("Reset did not drive state/match to defaults");

  // State encoding must stay legal after reset
  assert property (state inside {S0,S1,S2})
    else $error("Illegal state encoding");

  // Transition function and match behavior (Mealy)
  // S0
  assert property ((state==S0 &&  data) |=> (state==S1 && !match))
    else $error("S0,data=1 transition/match error");
  assert property ((state==S0 && !data) |=> (state==S0 && !match))
    else $error("S0,data=0 transition/match error");

  // S1
  assert property ((state==S1 && !data) |=> (state==S2 && !match))
    else $error("S1,data=0 transition/match error");
  assert property ((state==S1 &&  data) |=> (state==S0 && !match))
    else $error("S1,data=1 transition/match error");

  // S2
  assert property ((state==S2 && !data) |=> (state==S0 && !match))
    else $error("S2,data=0 transition/match error");
  assert property ((state==S2 &&  data) |=> (state==S0 && match))
    else $error("S2,data=1 transition/match error");

  // Match only when preceding cycle was detection in S2 with data==1
  assert property (match |-> $past(!reset && state==S2 && data))
    else $error("Spurious match pulse");

  // Match is a single-cycle pulse
  assert property (match |=> !match)
    else $error("match not a single-cycle pulse");

  // Coverage
  cover property (@(posedge clk) reset ##1 !reset);
  cover property (match); // at least one detection
  cover property ((state==S0 &&  data) ##1 (state==S1 && !data) ##1 (state==S2 && data) ##1 (match && state==S0)); // full 1-0-1 detection path
  cover property ((state==S0 && !data) ##1 (state==S0)); // S0 hold
  cover property ((state==S1 &&  data) ##1 (state==S0)); // S1->S0 on 1
  cover property ((state==S1 && !data) ##1 (state==S2)); // S1->S2 on 0
  cover property ((state==S2 && !data) ##1 (state==S0)); // S2->S0 on 0
  cover property ((state==S2 &&  data) ##1 (match && state==S0)); // S2 detect

endmodule

// Bind to DUT (captures internal 'state' and parameters)
bind mealy_fsm_4bit_sequence_detection
  mealy_fsm_4bit_sequence_detection_sva
    #(.S0(S0), .S1(S1), .S2(S2))
    mealy_fsm_4bit_sequence_detection_sva_i
    (.clk(clk), .reset(reset), .data(data), .match(match), .state(state));