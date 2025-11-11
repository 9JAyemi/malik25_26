// SVA for clock_gate: ENCLK is a registered AND of EN & TE, no glitches, no Xs.
// Bind into the DUT; no reset present, so we guard first cycle with past_valid.
`ifndef SYNTHESIS
module clock_gate_sva(input CLK, EN, TE, ENCLK);
  default clocking cb @(posedge CLK); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Inputs/output are 0/1 (no X/Z) at sampling
  assert property (past_valid |-> !$isunknown({EN, TE, ENCLK}));

  // Functional equivalence: registered AND
  assert property (past_valid |-> ENCLK == $past(EN && TE));

  // No mid-cycle glitches: output stable on the falling edge
  assert property (@(negedge CLK) $stable(ENCLK));

  // Cause/effect sanity on output edges
  assert property (past_valid && $rose(ENCLK) |-> $past(EN && TE));
  assert property (past_valid && $fell(ENCLK) |-> !$past(EN && TE));

  // Coverage: hit both output transitions and all input cases
  cover property (past_valid && (EN && TE) ##1 ENCLK);         // drives 1
  cover property (past_valid && !(EN && TE) ##1 !ENCLK);       // drives 0
  cover property (past_valid && $rose(ENCLK));
  cover property (past_valid && $fell(ENCLK));
  cover property (past_valid && $past({EN,TE}) == 2'b10 && !ENCLK); // EN=1,TE=0 -> 0
  cover property (past_valid && $past({EN,TE}) == 2'b01 && !ENCLK); // EN=0,TE=1 -> 0
  cover property (past_valid && $past({EN,TE}) == 2'b00 && !ENCLK); // EN=0,TE=0 -> 0
endmodule

bind clock_gate clock_gate_sva sva_i(.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));
`endif