// SVA for d_ff_sync_reset: concise, high-quality checks and coverage
module d_ff_sync_reset_sva (input logic CLK, D, RESET, Q, Q_N);

  default clocking cb @(posedge CLK); endclocking

  // Guard for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Basic functional correctness
  assert property (Q_N == ~Q)
    else $error("Q_N is not complement of Q");

  assert property (RESET |-> (Q == 1'b0 && Q_N == 1'b1))
    else $error("RESET must synchronously clear Q to 0 and Q_N to 1");

  assert property (past_valid && !RESET |-> (Q == $past(D)))
    else $error("Q must capture D on each rising edge when not in RESET");

  // No unintended changes
  assert property (past_valid && !RESET && (D == $past(D)) |-> (Q == $past(Q)))
    else $error("Q changed without D change when not in RESET");

  assert property (past_valid && (Q != $past(Q)) |-> (RESET || (!RESET && (D != $past(D)))))
    else $error("Q changed for a reason other than RESET or D change");

  // X/Z checks at clock edge
  assert property (!$isunknown({Q, Q_N}))
    else $error("Output X/Z detected on Q/Q_N at clock edge");

  assert property (!$isunknown({D, RESET}))
    else $warning("Input X/Z detected on D/RESET at clock edge");

  // Coverage: reset observed, and both output toggle directions when not in RESET
  cover property (RESET);
  cover property (past_valid && !RESET && $rose(Q));
  cover property (past_valid && !RESET && $fell(Q));
  // Priority scenario covered: RESET high with D high
  cover property (RESET && D);

endmodule

bind d_ff_sync_reset d_ff_sync_reset_sva sva_i (.*);