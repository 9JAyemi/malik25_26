// SVA for fsm_4bit_sequence_detection
// Bind-friendly, concise, and checks key behavior with coverage

module fsm_4bit_sequence_detection_sva
(
  input logic        clk,
  input logic        reset,
  input logic [3:0]  data,
  input logic        match,
  input logic [1:0]  state,
  input logic [1:0]  next_state
);

  // Local mirror of DUT encodings
  localparam logic [1:0] STATE_0 = 2'b00;
  localparam logic [1:0] STATE_1 = 2'b01;
  localparam logic [1:0] STATE_2 = 2'b10;
  localparam logic [1:0] STATE_3 = 2'b11;

  default clocking cb @(posedge clk); endclocking

  // Golden next-state and match functions
  function automatic logic [1:0] f_next (input logic [1:0] s, input logic [3:0] d);
    unique case (s)
      STATE_0: f_next = (d==4'b0001) ? STATE_1 : STATE_0;
      STATE_1: f_next = (d==4'b0010) ? STATE_2 : STATE_0;
      STATE_2: f_next = (d==4'b0100) ? STATE_3 : STATE_0;
      default: f_next = STATE_0; // STATE_3 -> STATE_0
    endcase
  endfunction

  function automatic bit f_match (input logic [1:0] s, input logic [3:0] d);
    return (s==STATE_2) && (d==4'b0100);
  endfunction

  // Basic sanity
  assert property (!$isunknown(state) && !$isunknown(match));
  assert property (state inside {STATE_0,STATE_1,STATE_2,STATE_3});

  // Reset behavior
  assert property (reset |-> state==STATE_0);

  // Combinational correctness
  assert property (next_state == f_next(state, data));
  assert property (match == f_match(state, data));

  // Registered state update
  assert property ($past(!reset) |-> state == $past(next_state));
  assert property ($past(!reset) |-> state == f_next($past(state), $past(data)));

  // Transition correctness (registered)
  assert property (disable iff (reset) (state==STATE_0 && data!=4'b0001) |=> state==STATE_0);
  assert property (disable iff (reset) (state==STATE_0 && data==4'b0001) |=> state==STATE_1);

  assert property (disable iff (reset) (state==STATE_1 && data!=4'b0010) |=> state==STATE_0);
  assert property (disable iff (reset) (state==STATE_1 && data==4'b0010) |=> state==STATE_2);

  assert property (disable iff (reset) (state==STATE_2 && data!=4'b0100) |=> state==STATE_0);
  assert property (disable iff (reset) (state==STATE_2 && data==4'b0100) |=> state==STATE_3);

  assert property (disable iff (reset) state==STATE_3 |=> state==STATE_0);

  // Match is a single-cycle pulse
  assert property (match |=> !match);

  // Coverage: full sequence and key transitions
  cover property (disable iff (reset)
    (state==STATE_0 && data==4'b0001) ##1
    (state==STATE_1 && data==4'b0010) ##1
    (state==STATE_2 && data==4'b0100 && match) ##1
    (state==STATE_3) ##1
    (state==STATE_0)
  );

  cover property (disable iff (reset) (state==STATE_3 && data==4'b1000) |=> state==STATE_0);

endmodule

// Bind into DUT (tool may require this in a separate file)
bind fsm_4bit_sequence_detection
  fsm_4bit_sequence_detection_sva sva
  (
    .clk(clk),
    .reset(reset),
    .data(data),
    .match(match),
    .state(state),
    .next_state(next_state)
  );