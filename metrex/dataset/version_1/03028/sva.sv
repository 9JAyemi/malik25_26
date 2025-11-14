// SVA for Clock_Gate
// Bind example: bind Clock_Gate Clock_Gate_sva cg_sva(.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));

module Clock_Gate_sva (
  input CLK,
  input EN,
  input TE,
  input ENCLK
);

  default clocking cb @(posedge CLK); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1'b1;

  // X-checks on key signals at sampling edges
  assert property (@cb !$isunknown(EN));
  assert property (@cb past_valid |-> !$isunknown(ENCLK));

  // Functional: ENCLK is the registered value of EN
  assert property (@cb past_valid |-> ENCLK == $past(EN));

  // No glitching: ENCLK may only change coincident with a CLK posedge
  assert property (@(posedge ENCLK or negedge ENCLK) $rose(CLK));

  // Minimal coverage
  // Exercise both functional paths and both ENCLK edges
  cover property (@cb past_valid && $rose(EN) ##1 ENCLK);
  cover property (@cb past_valid && $fell(EN) ##1 !ENCLK);
  cover property (@cb past_valid && ENCLK && !$past(ENCLK)); // ENCLK rise at posedge
  cover property (@cb past_valid && !ENCLK && $past(ENCLK)); // ENCLK fall at posedge

  // TE is present but unused in RTL; cover its activity to ensure stimulus hits it
  cover property (@cb $rose(TE));
  cover property (@cb $fell(TE));

endmodule