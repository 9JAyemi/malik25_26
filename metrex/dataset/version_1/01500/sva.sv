// SVA for debounce. Bind to DUT; checks key invariants and provides concise coverage.

module debounce_sva #(
  parameter int unsigned pCLKS = 32'(1_000_000)
) (
  input  logic   iCLK,
  input  logic   iRESET,
  input  logic   iSIG,
  input  logic   oSIG,
  ref    integer debounceCtr
);

  default clocking cb @(posedge iCLK); endclocking
  default disable iff (iRESET);

  // Async reset forces clear immediately
  assert property (@(posedge iRESET) ##0 (oSIG == 0 && debounceCtr == 0));

  // Counter bounds
  assert property (debounceCtr >= 0 && debounceCtr <= pCLKS);

  // If previously equal, counter is zero now
  assert property ($past(iSIG == oSIG) |-> (debounceCtr == 0));

  // While counting (< pCLKS) last cycle, output cannot change this cycle
  assert property (($past(iSIG != oSIG) && $past(debounceCtr) < pCLKS) |-> !$changed(oSIG));

  // Counting step or abort-to-zero depending on current input
  assert property (
    ($past(iSIG != oSIG) && $past(debounceCtr) < pCLKS)
      |-> ( (iSIG != $past(oSIG) && debounceCtr == $past(debounceCtr) + 1) ||
            (iSIG == $past(oSIG) && debounceCtr == 0) )
  );

  // Toggle happens exactly at threshold, matches input, and counter clears
  assert property (
    ($past(iSIG != oSIG) && $past(debounceCtr) == pCLKS)
      |-> ($changed(oSIG) && oSIG == $past(iSIG) && debounceCtr == 0)
  );

  // Any output change must be due to prior input != output
  assert property ($changed(oSIG) |-> ($past(iSIG) != $past(oSIG)));

  // If input equals previous output now, counter must be zero now
  assert property ((iSIG == $past(oSIG)) |-> (debounceCtr == 0));

  // Basic coverage
  cover property ($rose(oSIG));
  cover property ($fell(oSIG));

  // Cover threshold-triggered toggle event
  cover property ( ($past(iSIG != oSIG) && $past(debounceCtr) == pCLKS) ##1 $changed(oSIG) );

  // Cover short high glitch rejected (output stays low)
  cover property ( (!oSIG && !iSIG) ##1 (iSIG && !oSIG)[*1:pCLKS] ##1 (!iSIG && !oSIG) );

  // Cover short low glitch rejected (output stays high)
  cover property ( (oSIG && iSIG) ##1 (!iSIG && oSIG)[*1:pCLKS] ##1 (iSIG && oSIG) );

endmodule

bind debounce debounce_sva #(.pCLKS(pCLKS))
  u_debounce_sva (.iCLK(iCLK), .iRESET(iRESET), .iSIG(iSIG), .oSIG(oSIG), .debounceCtr(debounceCtr));