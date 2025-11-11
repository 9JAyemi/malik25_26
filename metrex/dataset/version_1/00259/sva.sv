// Assertions and coverage for EdgeDelay
// Bind this file to the DUT:
//   bind EdgeDelay EdgeDelay_chk ed_chk();

checker EdgeDelay_chk;
  default clocking cb @(posedge clk); endclocking

  // 1) Edge detectors and diagOut behavior
  // posEdgeReg toggles only on posedge sigIn
  assert property (@(posedge sigIn) $changed(posEdgeReg));
  assert property (@(negedge sigIn) !$changed(posEdgeReg));

  // negEdgeReg toggles only on negedge sigIn
  assert property (@(negedge sigIn) $changed(negEdgeReg));
  assert property (@(posedge sigIn) !$changed(negEdgeReg));

  // diagOut mirrors negEdgeReg and toggles on negedge sigIn
  assert property (diagOut == negEdgeReg);
  assert property (@(negedge sigIn) $changed(diagOut));
  assert property (@(posedge sigIn) !$changed(diagOut));

  // 2) Timer (re)arm gating with MIN_WAIT and precedence
  // When a qualifying pos-edge is seen and MIN_WAIT satisfied, re-arm pos timer and capture edge
  assert property ( (posEdgeRegLast != posEdgeReg) && (posEdgeDelayTimer > MIN_WAIT)
                    |=> (posEdgeRegLast == $past(posEdgeReg)) && (posEdgeDelayTimer == 1) );

  // Do not re-arm pos timer too early
  assert property ( (posEdgeRegLast != posEdgeReg) && (posEdgeDelayTimer <= MIN_WAIT)
                    |=> (posEdgeRegLast == $past(posEdgeRegLast)) && (posEdgeDelayTimer != 0) );

  // When a qualifying neg-edge is seen and MIN_WAIT satisfied, re-arm neg timer and capture edge
  assert property ( (negEdgeRegLast != negEdgeReg) && (negEdgeDelayTimer > MIN_WAIT)
                    |=> (negEdgeRegLast == $past(negEdgeReg)) && (negEdgeDelayTimer == 1) );

  // Do not re-arm neg timer too early
  assert property ( (negEdgeRegLast != negEdgeReg) && (negEdgeDelayTimer <= MIN_WAIT)
                    |=> (negEdgeRegLast == $past(negEdgeRegLast)) && (negEdgeDelayTimer != 0) );

  // If both qualifying edges happen in the same clk, pos branch wins (due to if/else-if)
  assert property ( (posEdgeRegLast != posEdgeReg) && (negEdgeRegLast != negEdgeReg) &&
                    (posEdgeDelayTimer > MIN_WAIT) && (negEdgeDelayTimer > MIN_WAIT)
                    |=> (posEdgeRegLast == $past(posEdgeReg)) &&
                        (negEdgeRegLast == $past(negEdgeRegLast)) &&
                        (posEdgeDelayTimer == 1) &&
                        (negEdgeDelayTimer == $past(negEdgeDelayTimer)) );

  // 3) Timers saturate at waitCnt+1 (never exceed)
  assert property ( {1'b0,posEdgeDelayTimer} <= ({1'b0,waitCnt} + 1) );
  assert property ( {1'b0,negEdgeDelayTimer} <= ({1'b0,waitCnt} + 1) );

  // 4) Output transitions only when timers hit waitCnt (previous cycle)
  assert property ( $rose(sigOut) |->  $past(posEdgeDelayTimer == waitCnt) && !$past(negEdgeDelayTimer == waitCnt) );
  assert property ( $fell(sigOut) |->  $past(negEdgeDelayTimer == waitCnt) && !$past(posEdgeDelayTimer == waitCnt) );
  assert property ( !($past(posEdgeDelayTimer == waitCnt) && $past(negEdgeDelayTimer == waitCnt)) );

  // Also ensure equality implies correct driven value by next cycle
  assert property ( (posEdgeDelayTimer == waitCnt) |=> sigOut );
  assert property ( (negEdgeDelayTimer == waitCnt) |=> !sigOut );

  // 5) Functional coverage
  // Output edges
  cover property ($rose(sigOut));
  cover property ($fell(sigOut));

  // WaitCnt corner: zero-latency actions
  cover property ( (waitCnt == '0) && (posEdgeDelayTimer == waitCnt) ##1 sigOut );
  cover property ( (waitCnt == '0) && (negEdgeDelayTimer == waitCnt) ##1 !sigOut );

  // MIN_WAIT gating observed (too-early edges do not re-arm)
  cover property ( (posEdgeRegLast != posEdgeReg) && (posEdgeDelayTimer <= MIN_WAIT) );
  cover property ( (negEdgeRegLast != negEdgeReg) && (negEdgeDelayTimer <= MIN_WAIT) );

  // Both qualifying edges same cycle -> pos precedence
  cover property ( (posEdgeRegLast != posEdgeReg) && (negEdgeRegLast != negEdgeReg) &&
                   (posEdgeDelayTimer > MIN_WAIT) && (negEdgeDelayTimer > MIN_WAIT) );

  // Timed actions at equality
  cover property ( (posEdgeDelayTimer == waitCnt) ##1 sigOut );
  cover property ( (negEdgeDelayTimer == waitCnt) ##1 !sigOut );
endchecker