// SVA for ClkDiv_20Hz
// Bind into DUT to access internal clkCount and parameter cntEndVal

module ClkDiv_20Hz_sva #(parameter int unsigned CNT_END = 19'h493E0)
(
  input  logic        CLK,
  input  logic        RST,
  input  logic        CLKOUT,
  input  logic        CLKOUTn,
  input  logic [18:0] clkCount
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  // Basic sanity
  assert property (!$isunknown({CLKOUT, CLKOUTn, clkCount}));
  assert property (CLKOUTn == ~CLKOUT);

  // Synchronous reset takes effect next cycle
  assert property (RST |=> (CLKOUT == 1'b0 && clkCount == '0));

  // Normal counting: increment by 1, output stable while not at terminal count
  assert property ((clkCount != CNT_END) |=> (clkCount == $past(clkCount)+1 && CLKOUT == $past(CLKOUT)));

  // Wrap behavior: when reaching CNT_END, next cycle toggles and counter clears
  assert property ((clkCount == CNT_END) |=> (clkCount == '0 && CLKOUT != $past(CLKOUT)));

  // Output only toggles on wrap
  assert property ((CLKOUT != $past(CLKOUT)) |-> ($past(clkCount) == CNT_END));

  // Counter never exceeds terminal value
  assert property (clkCount <= CNT_END);

  // Optional stronger interval check (no early toggle): exact spacing between toggles
  assert property ((CLKOUT != $past(CLKOUT)) |-> $stable(CLKOUT)[*CNT_END] ##1 (CLKOUT != $past(CLKOUT)));

  // Coverage
  cover property ((clkCount == CNT_END) ##1 (clkCount == '0 && CLKOUT != $past(CLKOUT)));         // wrap event
  cover property ((CLKOUT != $past(CLKOUT)) ##(CNT_END+1) (CLKOUT != $past(CLKOUT)));             // exact toggle spacing
  cover property (RST ##1 (CLKOUT==0 && clkCount==0) ##[1:$] (clkCount==CNT_END));                // reset then first wrap

endmodule

// Bind into the DUT (tools evaluate parameter/ports in the DUT scope)
bind ClkDiv_20Hz ClkDiv_20Hz_sva #(.CNT_END(cntEndVal)) u_clkdiv_sva (
  .CLK(CLK),
  .RST(RST),
  .CLKOUT(CLKOUT),
  .CLKOUTn(CLKOUTn),
  .clkCount(clkCount)
);