// SVA for watchdog_timer. Bind this into the DUT.
module watchdog_timer_sva (watchdog_timer dut);

  default clocking cb @(posedge dut.clk); endclocking
  // Use default disable for functional checks; override for reset checks
  default disable iff (dut.rst);

  // Combinational mirror: output equals internal enable
  assert property (dut.wdt === dut.wdt_enable);

  // Synchronous reset behavior: load timer from time, clear wdt
  assert property (disable iff (1'b0)
                   dut.rst |=> (dut.timer == $past(dut.time) && dut.wdt == 1'b0));

  // When not enabled, timer must hold its value
  assert property (!dut.wdt |-> $stable(dut.timer));

  // When enabled and timer > 0, it decrements by exactly 1 and wdt stays high
  assert property (dut.wdt && (dut.timer > 0)
                   |=> (dut.timer == $past(dut.timer) - 1) && dut.wdt);

  // Hitting zero asserts wdt next cycle and timer sticks at zero (no underflow)
  assert property ((dut.timer == 0) |=> (dut.wdt && dut.timer == 0));

  // wdt can only rise when timer was zero
  assert property ($rose(dut.wdt) |-> ($past(dut.timer) == 8'd0));

  // Once wdt is high, it stays high until reset
  assert property ($rose(dut.wdt) |=> (dut.wdt until_with dut.rst));

  // Timer never increases between non-reset cycles
  assert property (! $past(dut.rst) |-> (dut.timer <= $past(dut.timer)));

  // No X/Zs after coming out of reset
  assert property (! $past(dut.rst) |-> !$isunknown({dut.timer, dut.wdt, dut.wdt_enable}));

  // Coverage

  // Observe wdt assertion
  cover property ($rose(dut.wdt));

  // Observe a decrement step while enabled (likely unreachable with current RTL)
  cover property (dut.wdt && (dut.timer > 0) ##1 (dut.timer == $past(dut.timer) - 1));

  // Demonstrate stuck condition: disabled with nonzero timer for 10 cycles
  cover property ((!dut.wdt && (dut.timer > 0)) [*10]);

  // Reset-to-immediate-timeout path: time==0 leads to wdt assertion after reset release
  cover property (disable iff (1'b0)
                  dut.rst ##1 (!dut.rst && dut.timer == 8'd0) ##1 dut.wdt);

endmodule

bind watchdog_timer watchdog_timer_sva sva_inst();