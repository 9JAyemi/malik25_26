// SVA checkers and binds for latch and clock_gate

// Checker for latch
module latch_sva (input logic CK, E, SE, ECK);
  default clocking cb @(posedge CK); endclocking
  logic past_v;
  initial past_v = 1'b0;
  always @(posedge CK) past_v <= 1'b1;

  // Functional correctness
  assert property (past_v && $past(SE) |-> ECK == $past(E));
  assert property (past_v && !$past(SE) |-> ECK == $past(ECK));
  assert property (past_v && $changed(ECK) |-> $past(SE));
  assert property (past_v |-> !$isunknown(ECK));

  // Simple functional coverage
  cover property (past_v && $past(SE) &&  $past(E) &&  ECK);
  cover property (past_v && $past(SE) && !$past(E) && !ECK);
  cover property (past_v && !$past(SE) && (ECK == $past(ECK)));
endmodule

bind latch latch_sva u_latch_sva (.CK(CK), .E(E), .SE(SE), .ECK(ECK));


// Checker for clock_gate
module clock_gate_sva (input logic CLK, EN, TE, ENCLK, input logic D, G);
  default clocking cb @(posedge CLK); endclocking
  logic past_v;
  initial past_v = 1'b0;
  always @(posedge CLK) past_v <= 1'b1;

  // ENCLK must behave like a TE-gated register of EN (via internal latch)
  assert property (past_v && $past(TE) |-> ENCLK == $past(EN));
  assert property (past_v && !$past(TE) |-> ENCLK == $past(ENCLK));
  assert property (past_v && $changed(ENCLK) |-> $past(TE));
  assert property (past_v |-> !$isunknown(ENCLK));

  // Internal consistency
  assert property (G === (EN & TE));         // combinational relation holds
  assert property (past_v |-> D == $past(G)); // D captures G at each CLK edge

  // Simple functional coverage
  cover property (past_v && $past(TE) &&  $past(EN) &&  ENCLK);
  cover property (past_v && $past(TE) && !$past(EN) && !ENCLK);
  cover property (past_v && !$past(TE) && (ENCLK == $past(ENCLK)));
endmodule

bind clock_gate clock_gate_sva u_clock_gate_sva (.CLK(CLK), .EN(EN), .TE(TE), .ENCLK(ENCLK), .D(D), .G(G));