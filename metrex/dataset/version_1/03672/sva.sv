// SVA for d_ff_reset_enable
// Concise, high-quality checks and coverage

module d_ff_reset_enable_sva (
  input logic CLK,
  input logic D,
  input logic RESET_N,
  input logic ENABLE,
  input logic Q,
  input logic Q_N
);

  default clocking cb @(posedge CLK); endclocking

  // Make $past safe
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // Sanity: inputs known at use
  assert property (@cb !$isunknown(RESET_N))
    else $error("RESET_N is X/Z at clock edge");
  assert property (@cb RESET_N |-> !$isunknown({ENABLE,D}))
    else $error("ENABLE/D are X/Z when RESET_N=1");

  // Async reset: immediate clear and hold at 0 while asserted
  assert property (@(negedge RESET_N) ##0 (Q == 1'b0))
    else $error("Q not cleared immediately on async reset");
  assert property (@cb !RESET_N |-> (Q==1'b0 throughout (!RESET_N)))
    else $error("Q not held at 0 while RESET_N low");

  // Synchronous load/hold (guard first cycle)
  assert property (@cb disable iff(!past_valid) (RESET_N && ENABLE) |=> (Q == $past(D)))
    else $error("Q failed to load D when ENABLE=1");
  assert property (@cb disable iff(!past_valid) (RESET_N && !ENABLE) |=> (Q == $past(Q)))
    else $error("Q changed while ENABLE=0");

  // Change at clock implies cause (strong check)
  assert property (@cb disable iff(!past_valid) (RESET_N && (Q != $past(Q))) |-> (ENABLE && (Q == $past(D))))
    else $error("Q changed at clock without ENABLE or mismatched D");

  // Reset priority at clock
  assert property (@cb !RESET_N |=> (Q==1'b0))
    else $error("Q not 0 at clock under reset");

  // Complement output invariant at all events that can change Q/Q_N
  assert property (@(posedge CLK or negedge RESET_N or posedge RESET_N)
                   disable iff ($isunknown({Q,Q_N}))
                   (Q_N == ~Q))
    else $error("Q_N is not the complement of Q");

  // Functional coverage (concise but complete)
  // Reset pulse seen between clocks
  cover property (@cb past_valid && (!$past(RESET_N) && RESET_N));
  // Load 1
  cover property (@cb past_valid && RESET_N && ENABLE && ($past(Q)==1'b0) && (D==1'b1) |=> (Q==1'b1));
  // Load 0
  cover property (@cb past_valid && RESET_N && ENABLE && ($past(Q)==1'b1) && (D==1'b0) |=> (Q==1'b0));
  // Hold when disabled
  cover property (@cb past_valid && RESET_N && !ENABLE |=> (Q==$past(Q)));

endmodule

bind d_ff_reset_enable d_ff_reset_enable_sva sva_i (.*);