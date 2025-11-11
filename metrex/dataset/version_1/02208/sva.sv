// SVA for d_ff_en_gated
// Concise, high-quality checks and coverage
module d_ff_en_gated_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK
);
  default clocking cb @ (posedge CLK); endclocking

  // State equation of the registered output:
  // At each posedge, ENCLK must equal last cycle's (EN ? TE : 1'b0)
  property p_state_eq;
    ENCLK == ($past(EN,1,1'b0) ? $past(TE,1,1'b0) : 1'b0);
  endproperty
  assert property (p_state_eq);

  // Output must never be X/Z at the clock boundary
  assert property (!$isunknown(ENCLK));

  // Functional covers
  // Capture 1 when enabled
  cover property ($past(EN,1,1'b0) &&  $past(TE,1,1'b0) && ENCLK);
  // Capture 0 when enabled
  cover property ($past(EN,1,1'b0) && !$past(TE,1,1'b0) && !ENCLK);
  // Forced clear when disabled
  cover property (!$past(EN,1,1'b0) && !ENCLK);
  // Toggle while enabled across cycles
  cover property ($past(EN,1,1'b0) && $past(EN,2,1'b0) && (ENCLK != $past(ENCLK,1,1'b0)));
endmodule

// Bind into DUT
bind d_ff_en_gated d_ff_en_gated_sva u_d_ff_en_gated_sva (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK));