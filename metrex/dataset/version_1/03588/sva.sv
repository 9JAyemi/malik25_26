// SVA for PWMModule
// Bind this module to PWMModule: bind PWMModule PWMModule_sva sva();

// Concise, high-quality checks and coverage of key behaviors
module PWMModule_sva;

  // Use design scope (bind into PWMModule)
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // --------------------
  // Reset behavior (synchronous)
  // --------------------
  // After a reset cycle, everything is cleared on the next clock
  assert property (reset |=> counter==0 && threshold==0 && duty==0 && pwm==0 && done==0);

  // --------------------
  // Counter and done protocol
  // --------------------
  // Counter increments by 1 until 999; done stays 0 on non-wrap cycles
  assert property (counter!=999 |=> counter==$past(counter,1,reset)+1 && done==0);

  // Wrap at 999 causes counter=0 and done pulse
  assert property (counter==999 |=> counter==0 && done==1);

  // Counter is always within range
  assert property (counter<=999);

  // done is one-cycle pulse
  assert property (done |=> !done);

  // done only when previous counter was 999
  assert property (done |-> $past(counter,1,reset)==999);

  // done periodicity (exactly every 1000 cycles between pulses)
  assert property (done |=> !done[*999] ##1 done);

  // --------------------
  // Duty/thresh pipeline and PWM relation
  // --------------------
  // duty samples dutyCycle (one-cycle latency due to nonblocking)
  assert property (duty == $past(dutyCycle,1,reset));

  // threshold calculation matches RTL (with 8-bit truncation)
  assert property (
    threshold == (((256*($past(duty,1,reset)/100)) - 1) & 8'hFF)
  );

  // pwm reflects prior-cycle counter/threshold compare (due to nonblocking scheduling)
  assert property (pwm == ($past(counter,1,reset) < $past(threshold,1,reset)));

  // No X/Z on outputs
  assert property (!$isunknown({pwm,done}));

  // --------------------
  // Targeted coverage
  // --------------------
  // Observe wrap behavior
  cover property (counter==999 ##1 counter==0 && done);

  // Observe both pwm states
  cover property (pwm==1);
  cover property (pwm==0);

  // Boundary around threshold
  cover property (($past(counter,1,reset) == $past(threshold,1,reset)-1) && pwm);
  cover property (($past(counter,1,reset) == $past(threshold,1,reset)) && !pwm);

  // DutyCycle categories exercising division buckets
  cover property (dutyCycle==8'd0);
  cover property (dutyCycle==8'd99);
  cover property (dutyCycle==8'd100);
  cover property (dutyCycle==8'd199);
  cover property (dutyCycle==8'd200);
  cover property (dutyCycle==8'd255);

  // Two consecutive periods between done pulses
  cover property (done ##1 !done[*999] ##1 done);

endmodule