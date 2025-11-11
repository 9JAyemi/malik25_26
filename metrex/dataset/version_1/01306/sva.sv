// SVA for SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_11
// Bind into DUT with: bind SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_11 SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_11_sva u_sva (.*);

module SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_11_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK
);

  // Track valid past sample
  logic past_valid;
  always @(posedge CLK) past_valid <= 1'b1;

  // Inputs must be known at sampling
  assert property (@(posedge CLK) !$isunknown({EN,TE}))
    else $error("EN/TE unknown at CLK edge");

  // Output must be known after first cycle
  assert property (@(posedge CLK) past_valid |-> !$isunknown(ENCLK))
    else $error("ENCLK unknown");

  // Functional spec: ENCLK is registered EN && TE (1-cycle latency)
  assert property (@(posedge CLK) past_valid |-> ENCLK == $past(EN && TE))
    else $error("ENCLK != $past(EN&&TE)");

  // No glitches: ENCLK may only toggle on CLK rising edge (same time slot)
  assert property (@(posedge ENCLK) ##0 $rose(CLK))
    else $error("ENCLK rose without CLK rising");
  assert property (@(negedge ENCLK) ##0 $rose(CLK))
    else $error("ENCLK fell without CLK rising");

  // Coverage: observe both transitions and steady cases
  cover property (@(posedge CLK) past_valid && !$past(EN&&TE) && (EN&&TE) ##1 ENCLK);   // 0->1 causes ENCLK=1
  cover property (@(posedge CLK) past_valid &&  $past(EN&&TE) && !(EN&&TE) ##1 !ENCLK); // 1->0 causes ENCLK=0
  cover property (@(posedge CLK) past_valid &&  $past(EN&&TE) &&  (EN&&TE) ##1 ENCLK);  // hold-high
  cover property (@(posedge CLK) past_valid && !$past(EN&&TE) && !(EN&&TE) ##1 !ENCLK); // hold-low

endmodule

bind SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_11 SNPS_CLOCK_GATE_HIGH_d_ff_en_W32_0_11_sva u_sva (.*);