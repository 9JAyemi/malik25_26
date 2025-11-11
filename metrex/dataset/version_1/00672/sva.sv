// SVA for fsm_0101_sequence_detection
module fsm_0101_seqdet_sva #(
  parameter logic [1:0] STATE_IDLE   = 2'b00,
  parameter logic [1:0] STATE_WAIT_1 = 2'b01,
  parameter logic [1:0] STATE_WAIT_2 = 2'b10,
  parameter logic [1:0] STATE_MATCH  = 2'b11
)(
  input  logic        clk,
  input  logic        reset,
  input  logic        data,
  input  logic        match,
  input  logic [1:0]  state
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (checked even when reset is 1)
  assert property (disable iff (1'b0) (@cb reset |-> state == STATE_IDLE))
    else $error("State not IDLE during reset");

  // Registered next-state behavior (legal transitions)
  assert property (@cb (state==STATE_IDLE   && data==1'b0) |=> state==STATE_WAIT_1);
  assert property (@cb (state==STATE_IDLE   && data==1'b1) |=> state==STATE_IDLE);
  assert property (@cb (state==STATE_WAIT_1 && data==1'b1) |=> state==STATE_WAIT_2);
  assert property (@cb (state==STATE_WAIT_1 && data==1'b0) |=> state==STATE_IDLE);
  assert property (@cb (state==STATE_WAIT_2 && data==1'b0) |=> state==STATE_MATCH);
  assert property (@cb (state==STATE_WAIT_2 && data==1'b1) |=> state==STATE_IDLE);
  assert property (@cb (state==STATE_MATCH)                |=> state==STATE_IDLE);

  // Output correctness
  assert property (@cb match == (state==STATE_MATCH))
    else $error("match output not equal to (state==MATCH)");

  // Match only on the intended 010 pattern (starting from IDLE)
  assert property (@cb ((state==STATE_IDLE && data==1'b0) ##1 (data==1'b1) ##1 (data==1'b0))
                         |-> (state==STATE_MATCH && match));

  // No spurious match: must be preceded by 0,1,0 and path origin at IDLE
  assert property (@cb match |-> ($past(state,3)==STATE_IDLE &&
                                  $past(data,3)==1'b0 && $past(data,2)==1'b1 && $past(data,1)==1'b0));

  // One-cycle pulse on match
  assert property (@cb $rose(match) |-> ##1 !match);

  // No X on critical signals after reset
  assert property (@cb !$isunknown(state) && !$isunknown(match));

  // Coverage: reachability of states
  cover property (@cb state==STATE_WAIT_1);
  cover property (@cb state==STATE_WAIT_2);
  cover property (@cb state==STATE_MATCH);

  // Coverage: each transition
  cover property (@cb (state==STATE_IDLE   && data==1'b0) ##1 (state==STATE_WAIT_1));
  cover property (@cb (state==STATE_WAIT_1 && data==1'b1) ##1 (state==STATE_WAIT_2));
  cover property (@cb (state==STATE_WAIT_2 && data==1'b0) ##1 (state==STATE_MATCH));
  cover property (@cb (state==STATE_MATCH)               ##1 (state==STATE_IDLE));

  // Coverage: full 010 detection event
  cover property (@cb (state==STATE_IDLE && data==1'b0) ##1 (data==1'b1) ##1 (data==1'b0) and match);

endmodule

// Bind to DUT (captures internal state)
bind fsm_0101_sequence_detection fsm_0101_seqdet_sva #(
  .STATE_IDLE(STATE_IDLE),
  .STATE_WAIT_1(STATE_WAIT_1),
  .STATE_WAIT_2(STATE_WAIT_2),
  .STATE_MATCH(STATE_MATCH)
) fsm_0101_seqdet_sva_i (
  .clk(clk),
  .reset(reset),
  .data(data),
  .match(match),
  .state(state)
);