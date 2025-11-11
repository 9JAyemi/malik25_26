// SVA for module: driver
// Bind this file to the DUT to observe internals without changing RTL.

module driver_sva;
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  // 1) State tracker
  assert property (cb disable iff (!past_valid)
    stateLast == $past(state));

  // 2) State change kicks off settle window
  assert property (cb disable iff (!past_valid)
    $changed(state) |=> (settleTimeFlag && settleTimeCntr == 3'd1));

  // 3) Settle counter counts up while active until done
  assert property (cb disable iff (!past_valid)
    (settleTimeFlag && (settleTimeCntr != SETTLE_TIME))
    |=> (settleTimeFlag && (settleTimeCntr == $past(settleTimeCntr) + 3'd1)));

  // 4) Settle done: hand off to enable window, counters/flags set as expected
  assert property (cb disable iff (!past_valid)
    (settleTimeFlag && (settleTimeCntr == SETTLE_TIME))
    |=> (!settleTimeFlag && enableOnFlag && (settleTimeCntr == 3'd0)
         && (enableOnCntr == 5'd1) && enableReg));

  // 5) Enable window counts up and holds enable high while active
  assert property (cb disable iff (!past_valid)
    (enableOnFlag && (enableOnCntr != ENABLE_ON_TIME))
    |=> (enableOnFlag && (enableOnCntr == $past(enableOnCntr) + 5'd1) && enableReg));

  // 6) Enable window completes then clears next cycle
  assert property (cb disable iff (!past_valid)
    (enableOnFlag && (enableOnCntr == ENABLE_ON_TIME))
    |=> (!enableOnFlag && (enableOnCntr == 5'd0) && !enableReg));

  // 7) Basic invariants
  assert property (cb enable == enableReg);
  assert property (cb disable iff (!past_valid) enableReg |-> enableOnFlag);
  assert property (cb !settleTimeFlag |-> (settleTimeCntr == 3'd0));
  assert property (cb !enableOnFlag  |-> (enableOnCntr  == 5'd0));
  assert property (cb settleTimeCntr <= SETTLE_TIME);
  assert property (cb enableOnCntr   <= ENABLE_ON_TIME);

  // Coverage: full sequence and key corner cases
  cover property (cb disable iff (!past_valid)
    $changed(state)
    ##1 (settleTimeFlag && settleTimeCntr == 3'd1)
    ##[1:SETTLE_TIME-1] settleTimeFlag
    ##1 (!settleTimeFlag && enableOnFlag && enableOnCntr == 5'd1 && enableReg)
    ##[1:ENABLE_ON_TIME-1] (enableOnFlag && enableReg)
    ##1 (!enableOnFlag && !enableReg));

  // State change during enable window
  cover property (cb disable iff (!past_valid)
    (enableOnFlag && (enableOnCntr inside {[5'd1:ENABLE_ON_TIME-1]}))
    ##1 $changed(state));

  // State bounce during settle window
  cover property (cb disable iff (!past_valid)
    (settleTimeFlag && (settleTimeCntr inside {[3'd1:SETTLE_TIME-1]}))
    ##1 $changed(state));
endmodule

bind driver driver_sva d_sva();