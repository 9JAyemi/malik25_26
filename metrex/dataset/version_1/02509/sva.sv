// Bind these assertions into the DUT
bind pulse_generator pulse_generator_sva #(.WIDTH(WIDTH)) u_pulse_generator_sva();

module pulse_generator_sva #(parameter WIDTH=8) ();

  // Known-value checks (at every clock)
  assert property (@(posedge clock) !$isunknown({reset, enable, strobe_fast, rate}));
  assert property (@(posedge clock) !$isunknown(counter));
  assert property (@(posedge clock) !$isunknown(strobe_slow));

  // Combinational definition checks
  assert property (@(posedge clock) strobe_slow == ((counter == 1) && enable && strobe_fast));
  assert property (@(posedge clock) now == (counter == 1));

  // Reset behavior
  assert property (@(posedge clock) reset |=> counter == '0);
  assert property (@(posedge clock) reset |-> !strobe_slow);

  // Update rules
  // When not enabled, reload to current rate every cycle
  assert property (@(posedge clock) !reset && !enable |=> counter == rate);
  // When enabled but no fast strobe, hold value
  assert property (@(posedge clock) !reset && enable && !strobe_fast |=> counter == $past(counter));
  // When enabled and fast strobe, decrement unless at terminal count
  assert property (@(posedge clock) !reset && enable && strobe_fast && counter != 1 |=> counter == $past(counter) - 1);
  // When enabled and fast strobe at terminal count, reload
  assert property (@(posedge clock) !reset && enable && strobe_fast && counter == 1 |=> counter == rate);

  // strobe_slow is necessary and sufficient at terminal count with enable and fast strobe
  assert property (@(posedge clock) strobe_slow |-> (enable && strobe_fast && counter == 1));
  assert property (@(posedge clock) (enable && strobe_fast && counter == 1) |-> strobe_slow);

  // Coverage
  // Observe any slow strobe pulse
  cover  property (@(posedge clock) disable iff (reset) strobe_slow);
  // Observe reload via ~enable path
  cover  property (@(posedge clock) disable iff (reset) !enable ##1 counter == rate);
  // Observe terminal reload (counter==1 on strobe_fast, then reload)
  cover  property (@(posedge clock) disable iff (reset) enable && strobe_fast && counter == 1 ##1 counter == rate);
  // One complete slow period for a concrete example rate=3 (if reachable)
  cover  property (@(posedge clock) disable iff (reset)
                   enable && strobe_fast && counter == 1 && rate == 3
                   ##1 (enable && strobe_fast && rate == 3)[*2] ##1 strobe_slow);

endmodule