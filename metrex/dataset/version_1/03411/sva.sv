// SVA checker for fsm_4bit_sequence_detection (quality-focused, concise)
// Bind this checker to the DUT instance.
// It verifies reset behavior, legal transitions, shift_reg update semantics,
// and match generation/stickiness. It also provides targeted coverage.

module fsm_4bit_sequence_detection_chk (
  input  logic        clk,
  input  logic        reset,
  input  logic        data,
  input  logic [1:0]  state,
  input  logic [3:0]  shift_reg,
  input  logic        match
);
  // Encodings as used by DUT
  localparam logic [1:0] IDLE = 2'b00;
  localparam logic [1:0] S1   = 2'b01;
  localparam logic [1:0] S2   = 2'b10;
  localparam logic [1:0] S3   = 2'b11;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity (no X/Z on sampled cycle when out of reset)
  a_no_x: assert property (disable iff (!reset)
    !$isunknown({data, state, shift_reg, match})
  );

  // Asynchronous reset holds values
  a_async_reset_vals: assert property (
    !reset |-> (state==IDLE && shift_reg==4'b0 && match==1'b0)
  );

  // State transitions
  a_t_idle_0: assert property (disable iff(!reset)
    $past(state)==IDLE && $past(data)==1'b0 |=> state==IDLE
  );
  a_t_idle_1: assert property (disable iff(!reset)
    $past(state)==IDLE && $past(data)==1'b1 |=> state==S1
  );
  a_t_s1_0: assert property (disable iff(!reset)
    $past(state)==S1 && $past(data)==1'b0 |=> state==IDLE
  );
  a_t_s1_1: assert property (disable iff(!reset)
    $past(state)==S1 && $past(data)==1'b1 |=> state==S2
  );
  a_t_s2_0: assert property (disable iff(!reset)
    $past(state)==S2 && $past(data)==1'b0 |=> state==IDLE
  );
  a_t_s2_1: assert property (disable iff(!reset)
    $past(state)==S2 && $past(data)==1'b1 |=> state==S3
  );
  a_t_s3_any: assert property (disable iff(!reset)
    $past(state)==S3 |=> state==IDLE
  );

  // Shift register update
  a_shift_idle0_clears: assert property (disable iff(!reset)
    $past(state)==IDLE && $past(data)==1'b0 |=> shift_reg==4'b0000
  );
  a_shift_else_shift_in: assert property (disable iff(!reset)
    !($past(state)==IDLE && $past(data)==1'b0)
    |=> shift_reg == { $past(shift_reg)[2:0], $past(data) }
  );

  // match semantics
  // Asserted when S3 with data==1 (the 4th consecutive '1')
  a_match_set: assert property (disable iff(!reset)
    $past(state)==S3 && $past(data)==1'b1 |=> match==1'b1
  );
  // match can only rise on S3 + data==1
  a_match_rise_only_there: assert property (disable iff(!reset)
    $rose(match) |-> ($past(state)==S3 && $past(data)==1'b1)
  );
  // match never falls except due to async reset asserted between samples
  a_match_never_falls_without_reset: assert property (
    $fell(match) |-> (!reset || !$past(reset))
  );
  // match is sticky while out of reset
  a_match_sticky: assert property (disable iff(!reset)
    $past(match) |-> match
  );

  // Functional cover: detect 1111 sequence and match asserted
  c_detect_1111: cover property (disable iff(!reset)
    (state==IDLE && data==1) ##1
    (state==S1   && data==1) ##1
    (state==S2   && data==1) ##1
    (state==S3   && data==1) ##1
    (state==IDLE && match==1)
  );

  // Cover: zero resets the chain from S1/S2/S3 back to IDLE with a shift of 0
  c_zero_resets_path: cover property (disable iff(!reset)
    (state inside {S1,S2,S3} && data==0) ##1 (state==IDLE && shift_reg[0]==0)
  );

  // Cover: reach every state
  c_reach_idle: cover property (disable iff(!reset) state==IDLE);
  c_reach_s1:   cover property (disable iff(!reset) state==S1);
  c_reach_s2:   cover property (disable iff(!reset) state==S2);
  c_reach_s3:   cover property (disable iff(!reset) state==S3);

endmodule

// Bind to DUT (add once in a package or a top-level)
bind fsm_4bit_sequence_detection
  fsm_4bit_sequence_detection_chk u_fsm_4bit_sequence_detection_chk (
    .clk       (clk),
    .reset     (reset),
    .data      (data),
    .state     (state),
    .shift_reg (shift_reg),
    .match     (match)
  );