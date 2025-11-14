// SVA for SNPS_CLOCK_GATE_HIGH_RegisterAdd_W6_87
// Concise checks for functional correctness, edge alignment, X safety, and basic coverage.

module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W6_87_sva (
  input logic CLK, EN, TE, ENCLK
);

  // Functional equivalence on any relevant change
  property p_func_equiv;
    @(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
      !$isunknown({CLK,EN,TE}) |-> (ENCLK === ((EN || TE) ? CLK : 1'b0));
  endproperty
  assert property (p_func_equiv);

  // Edge alignment when enabled
  assert property (@(posedge CLK) (EN || TE) |-> (ENCLK == 1'b1));
  assert property (@(negedge CLK) (EN || TE) |-> (ENCLK == 1'b0));

  // When disabled, output must be 0 across clock edges
  assert property (@(posedge CLK or negedge CLK) (!EN && !TE) |-> (ENCLK == 1'b0));

  // Output toggles only if a driver toggles
  assert property (@(posedge ENCLK or negedge ENCLK)
                     ($changed(CLK) || $changed(EN) || $changed(TE)));

  // No X on output when inputs are known
  assert property (@(posedge CLK or negedge CLK or posedge EN or negedge EN or posedge TE or negedge TE)
                     (!$isunknown({CLK,EN,TE})) |-> (!$isunknown(ENCLK)));

  // Coverage: exercise all enable combinations
  cover property (@(posedge CLK)  EN && !TE);
  cover property (@(posedge CLK) !EN &&  TE);
  cover property (@(posedge CLK)  EN &&  TE);
  cover property (@(posedge CLK) !EN && !TE);

  // Coverage: see gated clock edges while enabled
  cover property (@(posedge CLK) (EN || TE) && $rose(ENCLK));
  cover property (@(negedge CLK) (EN || TE) && $fell(ENCLK));

endmodule

bind SNPS_CLOCK_GATE_HIGH_RegisterAdd_W6_87
  SNPS_CLOCK_GATE_HIGH_RegisterAdd_W6_87_sva u_sva (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));