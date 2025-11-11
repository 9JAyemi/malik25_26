// SVA for clock_gating
module clock_gating_sva (input logic CLK, EN, TE, ENCLK);

  default clocking cb @(posedge CLK); endclocking

  // Functional next-cycle behavior
  assert property ( (TE || EN) |=> ENCLK );
  assert property ( (!TE && !EN) |=> !ENCLK );

  // No X on output (synchronous check)
  assert property ( !$isunknown(ENCLK) );

  // No mid-cycle glitches (output updates only at posedge CLK)
  assert property (@(negedge CLK) $stable(ENCLK));

  // Coverage: exercise TE, EN, and off paths; observe both output transitions
  cover property ( (!TE && EN) |=> ENCLK );
  cover property ( (TE && !EN) |=> ENCLK );
  cover property ( (!TE && !EN) |=> !ENCLK );
  cover property ( !ENCLK ##1 ENCLK );
  cover property ( ENCLK ##1 !ENCLK );

endmodule

bind clock_gating clock_gating_sva cg_sva (.*);