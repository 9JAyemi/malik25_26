// SVA for SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_4
// Function: On each posedge CLK, if EN=1 then ENCLK samples TE; else ENCLK=0.

module SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_4_sva
(
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK
);

  // establish safe use of $past
  bit past_valid;
  initial past_valid = 0;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  default clocking cb @(posedge CLK); endclocking

  // Functional mapping (forward)
  assert property (disable iff (!past_valid)
    EN |-> ##1 (ENCLK == $past(TE))
  );
  assert property (disable iff (!past_valid)
    !EN |-> ##1 (ENCLK == 1'b0)
  );

  // Functional consistency (backward)
  assert property (disable iff (!past_valid)
    ENCLK |-> $past(EN && TE)
  );
  assert property (disable iff (!past_valid)
    !ENCLK |-> $past(!EN || !TE)
  );

  // No mid-cycle change (basic check at negedge)
  assert property (@(negedge CLK) $stable(ENCLK));

  // X-checks
  assert property (disable iff (!past_valid) !$isunknown({EN,TE}));
  assert property (disable iff (!past_valid) !$isunknown(ENCLK));

  // Coverage
  cover property (EN && TE);
  cover property (EN && !TE);
  cover property (!EN);

  cover property ($rose(ENCLK));
  cover property ($fell(ENCLK));

  // Output follows TE while enabled (rise then fall cases)
  cover property (EN && !TE ##1 EN && TE ##1 (ENCLK==1));
  cover property (EN && TE ##1 EN && !TE ##1 (ENCLK==0));

endmodule

bind SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_4 SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_4_sva
  i_SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_4_sva(.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));