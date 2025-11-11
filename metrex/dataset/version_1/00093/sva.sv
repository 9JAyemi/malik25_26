// SVA for clock_gate. Bind to your DUT instance(s).
module clock_gate_sva (input logic CLK, EN, TE, ENCLK);

  default clocking cb @(posedge CLK or negedge CLK); endclocking
  default disable iff ($isunknown(CLK));

  // Output must be low whenever CLK is low (no glitches when CLK=0)
  assert property (!CLK |-> (ENCLK == 1'b0));

  // ENCLK may only change on CLK edges
  assert property ($changed(ENCLK) |-> ($rose(CLK) or $fell(CLK)));

  // Edge alignment
  assert property ($rose(ENCLK) |-> $rose(CLK));
  assert property ($fell(ENCLK) |-> $fell(CLK));

  // After a rising edge of CLK, ENCLK equals EN && !TE for the high phase
  assert property ($rose(CLK) |-> ##0 (ENCLK === (EN && !TE)));

  // Basic sanity: output not X/Z at clock edges
  assert property (!$isunknown(ENCLK));

  // Coverage: pass and block scenarios
  cover property ($rose(CLK) and (EN && !TE) ##0 $rose(ENCLK) ##1 $fell(ENCLK));
  cover property ($rose(CLK) and (!EN || TE) ##0 !ENCLK);

endmodule

// Bind to all instances of clock_gate
bind clock_gate clock_gate_sva cg_sva_i (.*);