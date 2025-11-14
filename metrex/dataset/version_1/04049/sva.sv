// SVA for clock_divider
// Bind this module to the DUT: bind clock_divider clock_divider_sva sva();

module clock_divider_sva (clock_divider dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (!dut.reset);

  // Async reset values must hold while reset is low
  assert property ( !dut.reset |-> (dut.refresh_clk==1'b1 && dut.sys_clk==1'b0 &&
                                    dut.counter1==9'd0 && dut.counter2==9'd63 &&
                                    dut.clk_divid==9'd100) );

  // clk_divid must never change after reset releases
  assert property ( $past(dut.reset) |-> dut.clk_divid == $past(dut.clk_divid) );

  // Counters stay within range
  assert property ( dut.counter1 <= dut.clk_divid );
  assert property ( dut.counter2 <= dut.clk_divid );

  // Hold behavior when disabled
  assert property ( !dut.enabled |-> $stable(dut.refresh_clk) && $stable(dut.sys_clk) &&
                                   $stable(dut.counter1)    && $stable(dut.counter2) &&
                                   $stable(dut.clk_divid) );

  // Counting behavior when enabled and below terminal count
  assert property ( dut.enabled && (dut.counter1 < dut.clk_divid)
                    |=> dut.counter1 == $past(dut.counter1)+1 &&
                        dut.refresh_clk == $past(dut.refresh_clk) );
  assert property ( dut.enabled && (dut.counter2 < dut.clk_divid)
                    |=> dut.counter2 == $past(dut.counter2)+1 &&
                        dut.sys_clk == $past(dut.sys_clk) );

  // Terminal count: toggle and reset counter
  assert property ( dut.enabled && (dut.counter1 == dut.clk_divid)
                    |=> dut.counter1 == 9'd0 &&
                        dut.refresh_clk != $past(dut.refresh_clk) );
  assert property ( dut.enabled && (dut.counter2 == dut.clk_divid)
                    |=> dut.counter2 == 9'd0 &&
                        dut.sys_clk != $past(dut.sys_clk) );

  // No unexpected output toggles (must occur only on terminal count while enabled)
  assert property ( $changed(dut.refresh_clk)
                    |-> $past(dut.enabled) && ($past(dut.counter1) == $past(dut.clk_divid)) );
  assert property ( $changed(dut.sys_clk)
                    |-> $past(dut.enabled) && ($past(dut.counter2) == $past(dut.clk_divid)) );

  // Coverage
  cover property ( $changed(dut.refresh_clk) );
  cover property ( $changed(dut.sys_clk) );
  cover property ( dut.enabled && (dut.counter1 == dut.clk_divid)
                   ##1 (dut.counter1 == 9'd0) );
  cover property ( !dut.enabled && $stable(dut.refresh_clk) && $stable(dut.sys_clk) );

endmodule