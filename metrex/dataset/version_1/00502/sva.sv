// SVA for sequence_detector
module sequence_detector_sva (
  input  logic        clock,
  input  logic        clear,
  input  logic        switch,
  input  logic [1:0]  state,
  input  logic        request
);
  localparam logic [1:0] state_a = 2'b00, state_b = 2'b01, state_c = 2'b10;

  default clocking cb @(posedge clock); endclocking

  // Sync clear behavior
  assert property (@(posedge clock) clear |=> (state==state_a && request==0));

  // State encoding always legal
  assert property (@(posedge clock) state inside {state_a, state_b, state_c});

  // Next-state function and request generation
  default disable iff (clear);
  assert property (state==state_a &&  switch |=> state==state_b);
  assert property (state==state_a && !switch |=> state==state_a);

  assert property (state==state_b && !switch |=> state==state_c);
  assert property (state==state_b &&  switch |=> state==state_b);

  assert property (state==state_c &&  switch |=> state==state_a && request);
  assert property (state==state_c && !switch |=> state==state_c);

  // Request cannot deassert without clear
  assert property (request |=> request);

  // Request can only be set by the state_c && switch event
  assert property ((request==0 && !(state==state_c && switch)) |=> request==0);

  // Causality: any request rise must be due to (state_c && switch) in prior cycle
  assert property (@(posedge clock) $rose(request) |-> ($past(state)==state_c && $past(switch) && !$past(clear)));

  // Coverage
  sequence detect_seq;
    (state==state_a && switch) ##1 (state==state_b && !switch) ##1 (state==state_c && switch);
  endsequence

  cover property (disable iff (clear) detect_seq ##1 request);
  cover property (disable iff (clear) state==state_a && !switch ##1 state==state_a);
  cover property (disable iff (clear) state==state_b &&  switch ##1 state==state_b);
  cover property (disable iff (clear) state==state_c && !switch ##1 state==state_c);
  cover property (@(posedge clock) $rose(request));
endmodule

// Bind into DUT
bind sequence_detector sequence_detector_sva sva_i (
  .clock  (clock),
  .clear  (clear),
  .switch (switch),
  .state  (state),
  .request(request)
);