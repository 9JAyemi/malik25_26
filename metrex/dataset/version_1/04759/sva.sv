// SVA for clock_gate
module clock_gate_sva (
  input logic CLK, EN, TE, RST,
  input logic ENCLK,
  input logic D
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  let en_te = EN & TE;

  // Functional correctness
  assert property (D == en_te);                                // D captures EN&TE each cycle
  assert property (!$past(RST) |-> ENCLK == $past(D));         // ENCLK is 1-cycle delayed D
  assert property ($past(RST) |-> ENCLK == 1'b0);              // First cycle after reset, ENCLK must be 0

  // Consistency checks between ENCLK and EN&TE
  assert property (ENCLK |-> (!$past(RST) && $past(en_te)));   // ENCLK high implies prior EN&TE high
  assert property ((!$past(RST) && !$past(en_te)) |-> !ENCLK); // Prior EN&TE low implies ENCLK low

  // Reset behavior
  assert property (@(posedge RST) (D==0 && ENCLK==0));         // Async clear on reset edge
  assert property (@(posedge CLK) RST |-> (D==0 && ENCLK==0)); // Hold clear while reset high

  // Glitchlessness: ENCLK only changes on CLK or RST edges
  assert property (@($global_clock) $changed(ENCLK) |-> ($rose(CLK) || $rose(RST)));

  // Coverage
  cover property ($rose(en_te) ##1 $rose(ENCLK));              // Rising propagation
  cover property ($fell(en_te) ##1 $fell(ENCLK));              // Falling propagation
  cover property (RST ##1 !RST ##1 ENCLK==0);                  // Reset release behavior

endmodule

bind clock_gate clock_gate_sva u_clock_gate_sva (
  .CLK(CLK), .EN(EN), .TE(TE), .RST(RST),
  .ENCLK(ENCLK),
  .D(D)
);