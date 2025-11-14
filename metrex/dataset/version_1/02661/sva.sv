// SVA for Timer
module Timer_sva (
  input  io_tick,
  input  io_clear,
  input  [15:0] io_limit,
  input  io_full,
  input  [15:0] io_value,
  input  io_mainClk,
  input  resetCtrl_systemReset,
  // internal DUT signals (accessible via bind)
  input  [15:0] counter,
  input  limitHit,
  input  inhibitFull
);

  // Combinational correctness
  assert property (@(posedge io_mainClk)) io_value == counter;
  assert property (@(posedge io_mainClk)) limitHit == (counter == io_limit);
  assert property (@(posedge io_mainClk)) io_full  == (limitHit && io_tick && !inhibitFull);

  // Asynchronous reset puts regs to 0 immediately
  assert property (@(posedge resetCtrl_systemReset))
    (counter == 16'h0000 && inhibitFull == 1'b0);

  // Clear dominates: next-cycle counter/inhibitFull go to 0
  assert property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    io_clear |=> (counter == 16'h0000 && inhibitFull == 1'b0);

  // Increment on tick when not clearing
  assert property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    (io_tick && !io_clear) |=> (counter == $past(counter) + 16'd1);

  // Hold when no tick and no clear
  assert property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    (!io_tick && !io_clear) |=> (counter == $past(counter) && inhibitFull == $past(inhibitFull));

  // inhibitFull updates to current limitHit on tick (when not clearing)
  assert property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    (io_tick && !io_clear) |=> (inhibitFull == $past(limitHit));

  // If full asserted (and not clearing), counter must have incremented
  assert property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    (io_full && !io_clear) |=> (counter == $past(counter) + 16'd1);

  // No back-to-back full pulses
  assert property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    io_full |-> ##1 !io_full;

  // Covers

  // Observe two full pulses separated by a re-arm tick where limitHit is false
  cover property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    io_full ##1 (io_tick && !limitHit) ##[1:$] io_full;

  // Wrap-around on increment
  cover property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    (io_value == 16'hFFFF && io_tick && !io_clear) ##1 (io_value == 16'h0000);

  // Full immediately after clear when limit is zero
  cover property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    io_clear ##1 (io_limit == 16'h0000 && io_tick && io_full);

  // Gating: full suppressed on next cycle even if limitHit stays high
  cover property (@(posedge io_mainClk) disable iff (resetCtrl_systemReset))
    io_full ##1 (io_tick && limitHit && inhibitFull && !io_full);

endmodule

bind Timer Timer_sva sva_inst (.*);