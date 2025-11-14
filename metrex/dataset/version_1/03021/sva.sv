// SVA for fsm_sequence_detection
// Bind example:
// bind fsm_sequence_detection fsm_sequence_detection_sva u_sva (.*);

module fsm_sequence_detection_sva (
  input logic        clk,
  input logic        reset,
  input logic        data,
  input logic        match,
  input logic [1:0]  state,
  input logic [1:0]  next_state
);
  localparam logic [1:0] S0 = 2'b00;
  localparam logic [1:0] S1 = 2'b01;
  localparam logic [1:0] S2 = 2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Asynchronous reset behavior
  always @(posedge reset) begin
    assert (state == S0) else $error("State not S0 at async reset");
  end
  assert property (@(posedge clk) reset |-> (state==S0 && match==1'b0));

  // Legal encodings
  assert property (state      inside {S0,S1,S2});
  assert property (next_state inside {S0,S1,S2});

  // Output correctness
  assert property (match == ((state==S2) && data));

  // Combinational next_state function
  assert property (state==S0 |-> next_state == (data ? S1 : S0));
  assert property (state==S1 |-> next_state == (data ? S2 : S0));
  assert property (state==S2 |-> next_state == S0);

  // Registered state transitions
  assert property ((state==S0 && !data) |=> state==S0);
  assert property ((state==S0 &&  data) |=> state==S1);
  assert property ((state==S1 && !data) |=> state==S0);
  assert property ((state==S1 &&  data) |=> state==S2);
  assert property ( state==S2            |=> state==S0);

  // Reverse reachability (guards against illegal jumps)
  assert property (state==S1 |-> $past(state)==S0 && $past(data));
  assert property (state==S2 |-> $past(state)==S1 && $past(data));

  // Match must be a single-cycle pulse
  assert property (match |=> !match);

  // Functional detection: three consecutive 1's cause a match on the third 1
  sequence three_ones; data ##1 data ##1 data; endsequence
  assert property (three_ones |-> match);

  // Coverage: exercise all transitions and the detect event
  cover property ((state==S0 && !data) ##1 state==S0);
  cover property ((state==S0 &&  data) ##1 state==S1);
  cover property ((state==S1 && !data) ##1 state==S0);
  cover property ((state==S1 &&  data) ##1 state==S2);
  cover property ( state==S2            ##1 state==S0);
  cover property (three_ones and match);

endmodule