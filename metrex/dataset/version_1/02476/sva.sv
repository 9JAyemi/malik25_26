// SVA for SNPS_CLOCK_GATE_HIGH_RegisterAdd_W17 and TLATNTSCAX2TS
// Focus: functional correctness, no-glitch, knownness, concise coverage

// Cell-level checker
module TLATNTSCAX2TS_sva (input logic CK, E, SE, ECK);
  logic started; initial started = 1'b0; always @(posedge CK) started <= 1'b1;
  default clocking cb @(posedge CK); endclocking

  // Functional update/hold
  a_update: assert property (disable iff (!started) E  |=> (ECK == $past(SE)));
  a_hold:   assert property (disable iff (!started) !E |=> (ECK == $past(ECK)));

  // No glitch: ECK may only change on CK rising edge
  a_no_glitch: assert property (@(posedge ECK or negedge ECK) $rose(CK));

  // Knownness
  a_E_known:   assert property (!$isunknown(E));
  a_SE_known_when_used: assert property (E |-> !$isunknown(SE));
  a_ECK_known_when_updated: assert property ((E && !$isunknown(SE)) |=> !$isunknown(ECK));

  // Minimal functional coverage
  c_capture0: cover property (started && E && (SE==1'b0) ##1 (ECK==1'b0));
  c_capture1: cover property (started && E && (SE==1'b1) ##1 (ECK==1'b1));
  c_hold:     cover property (started && !E ##1 $stable(ECK));
  c_follow:   cover property (started && E && (SE != $past(ECK)) ##1 (ECK == SE));
endmodule

// Top-level checker (integration and output glitching)
module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W17_sva (input logic CLK, EN, TE, ENCLK);
  logic started; initial started = 1'b0; always @(posedge CLK) started <= 1'b1;
  default clocking cb @(posedge CLK); endclocking

  a_EN_known: assert property (!$isunknown(EN));
  a_TE_known_when_used: assert property (EN |-> !$isunknown(TE));

  // Output must only toggle on CLK posedge
  a_ENCLK_no_glitch: assert property (@(posedge ENCLK or negedge ENCLK) $rose(CLK));

  // Integration coverage (both capture values)
  c_top_cap1: cover property (started && EN && TE    ##1 (ENCLK==1'b1));
  c_top_cap0: cover property (started && EN && !TE   ##1 (ENCLK==1'b0));
endmodule

// Bind the checkers
bind TLATNTSCAX2TS TLATNTSCAX2TS_sva u_tlat_sva (.*);
bind SNPS_CLOCK_GATE_HIGH_RegisterAdd_W17 SNPS_CLOCK_GATE_HIGH_RegisterAdd_W17_sva u_top_sva (.*);