// SVA for dff_asr – concise, high-quality checks and coverage
module dff_asr_sva (
  input logic D, CLK, SET_B, RESET_B,
  input logic Q, Q_N
);

  default clocking cb @(posedge CLK); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // Functional update with priority (SET over RESET) and data capture
  assert property (past_valid |-> Q ==
                    ( !$past(SET_B)    ? 1'b1 :
                      !$past(RESET_B)  ? 1'b0 :
                                         $past(D) ));

  // Complementary output relation
  assert property (Q_N === ~Q);

  // No X on Q when inputs were known on the sampling edge
  assert property (past_valid && !$isunknown($past({SET_B,RESET_B,D})) |-> !$isunknown(Q));

  // Explicit priority check when both controls asserted low
  assert property (past_valid && !$past(SET_B) && !$past(RESET_B) |-> Q == 1'b1);

  // Coverage: exercise all behaviors
  cover property (past_valid && !$past(SET_B)                        && Q == 1'b1); // set
  cover property (past_valid &&  $past(SET_B) && !$past(RESET_B)     && Q == 1'b0); // reset
  cover property (past_valid &&  $past(SET_B) &&  $past(RESET_B) && $past(D)==1'b0 && Q==1'b0); // capture 0
  cover property (past_valid &&  $past(SET_B) &&  $past(RESET_B) && $past(D)==1'b1 && Q==1'b1); // capture 1
  cover property (past_valid && !$past(SET_B) && !$past(RESET_B)     && Q == 1'b1); // both asserted, set wins
  cover property (past_valid &&  $past(SET_B) &&  $past(RESET_B)     && Q != $past(Q)); // data-driven toggle
  cover property (past_valid && $changed(Q) && $changed(Q_N)); // Q_N tracks Q on changes

endmodule

bind dff_asr dff_asr_sva sva_inst (.D(D), .CLK(CLK), .SET_B(SET_B), .RESET_B(RESET_B), .Q(Q), .Q_N(Q_N));