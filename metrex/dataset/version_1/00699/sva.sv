// SystemVerilog Assertions for the design
// Concise, quality-focused, with key checks and essential coverage
// Drop into a separate file and compile with DUT; uses bind per-module

// --------------- reg8 ---------------
module reg8_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  // Interface/intent
  assert property (out == register[7:0]);
  assert property (register[8] == 1'b0);

  // Sequencing
  assert property (ce |=> out == $past(in));
  assert property (!ce |=> out == $past(out));

  // Coverage
  cover property (ce ##1 out != $past(out));
endmodule
bind reg8 reg8_sva reg8_sva_i();


// --------------- divby1248 ---------------
module divby1248_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  // Counter behavior
  assert property (cein |=> counter == $past(counter) + 3'd1);
  assert property (!cein |=> counter == $past(counter));

  // ceout mapping and implications
  assert property (ceout |-> cein);
  assert property ((divisor == 2'b00) |-> ceout == cein);
  assert property ((divisor == 2'b01) |-> ceout == (cein & counter[0]));
  assert property ((divisor == 2'b10) |-> ceout == (cein & counter[0] & counter[1]));
  assert property ((divisor == 2'b11) |-> ceout == (cein & counter[0] & counter[1] & counter[2]));

  // Coverage: see a pulse for each divisor
  cover property (divisor==2'b00 && ceout);
  cover property (divisor==2'b01 && ceout);
  cover property (divisor==2'b10 && ceout);
  cover property (divisor==2'b11 && ceout);
endmodule
bind divby1248 divby1248_sva divby1248_sva_i();


// --------------- fixeddivby2 ---------------
module fixeddivby2_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  // Toggle only on cein
  assert property (cein |=> q == ~$past(q));
  assert property (!cein |=> q == $past(q));

  // Output relation
  assert property (ceout == (cein & q));
  assert property (ceout |-> cein);

  // Coverage
  cover property (cein throughout (##1 ceout));
endmodule
bind fixeddivby2 fixeddivby2_sva fixeddivby2_sva_i();


// --------------- fixeddivby32 ---------------
module fixeddivby32_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  // Counter behavior
  assert property (cein |=> counter == $past(counter) + 5'd1);
  assert property (!cein |=> counter == $past(counter));

  // Pulse is one-cycle wide
  assert property (ceout |=> !ceout);

  // ceout occurs exactly when previous cycle had cein with counter==31
  assert property (ceout == $past(cein && ($past(counter) == 5'd31)));

  // Coverage: see a ceout pulse
  cover property (ceout);
endmodule
bind fixeddivby32 fixeddivby32_sva fixeddivby32_sva_i();


// --------------- fixeddivby256 ---------------
module fixeddivby256_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  // Counter behavior
  assert property (cein |=> counter == $past(counter) + 8'd1);
  assert property (!cein |=> counter == $past(counter));

  // Pulse is one-cycle wide
  assert property (ceout |=> !ceout);

  // ceout occurs exactly when previous cycle had cein with counter==255
  assert property (ceout == $past(cein && ($past(counter) == 8'd255)));

  // Coverage: see a ceout pulse
  cover property (ceout);
endmodule
bind fixeddivby256 fixeddivby256_sva fixeddivby256_sva_i();


// --------------- wdtimer ---------------
module wdtimer_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  // Local guard
  function automatic bit guard_now;
    return (enable && !wdreset && !wdogdisreg);
  endfunction

  // wdogdisreg tracks input same cycle (blocking assignment in seq block)
  assert property (wdogdisreg == wdogdis);

  // Counter control
  assert property (!guard_now() |=> counter == 8'h00);
  assert property (guard_now() && cein |=> counter == $past(counter) + 8'd1);
  assert property (guard_now() && !cein |=> counter == $past(counter));

  // Trip pulse logic: registered from prior cycle’s combinational condition
  assert property (wdtripce == $past(cein && guard_now() && (counter == wdogdivreg)));

  // One-cycle pulse
  assert property (wdtripce |=> !wdtripce);

  // Coverage: see a trip
  cover property (wdtripce);
endmodule
bind wdtimer wdtimer_sva wdtimer_sva_i();


// --------------- wdregister ---------------
module wdregister_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  // Combinational outputs
  assert property (motorenaint == (~wdtrip & controlreg[3]));
  assert property (run0 == controlreg[0]);
  assert property (run1 == controlreg[1]);
  assert property (run2 == controlreg[2]);
  assert property (controlrdata == {wdtrip, wdogdis, 1'b0, 1'b0, controlreg[3:0]});

  // Control register write
  assert property (ctrlld |=> controlreg == $past(wrtdata));

  // wdtrip set/clear with priority: clear on ctrlld & wrtdata==8'h80
  assert property (wdtripce && !(ctrlld && (wrtdata==8'h80)) |=> wdtrip == 1'b1);
  assert property (ctrlld && (wrtdata==8'h80) |=> wdtrip == 1'b0);

  // If both assert same cycle, clear wins
  assert property (wdtripce && ctrlld && (wrtdata==8'h80) |=> wdtrip == 1'b0);

  // Coverage: see set then clear
  cover property (wdtripce ##1 ctrlld && (wrtdata==8'h80));
endmodule
bind wdregister wdregister_sva wdregister_sva_i();


// --------------- ledctr ---------------
module ledctr_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  assert property (ce |=> counter == $past(counter) + 10'd1);
  assert property (!ce |=> counter == $past(counter));
  assert property (ledalive == counter[9]);

  // Coverage: see ledalive toggle
  cover property ($changed(ledalive));
endmodule
bind ledctr ledctr_sva ledctr_sva_i();


// --------------- control (top) ---------------
module control_sva;
  default clocking cb @(posedge clk); endclocking
  bit past_v; initial past_v = 0; always @(posedge clk) past_v <= 1;
  default disable iff (!past_v);

  // Static and simple mapping
  assert property (tie1 == 1'b1);
  assert property (hwconfig == 8'h30);
  assert property (configrdreg0 == configreg0);
  assert property (configrdreg1 == configreg1);
  assert property (configrdreg2 == configreg2);

  // Config enables blocked by motor enable
  assert property (cfgce0 == (cfgld0 & ~motorenaint));
  assert property (cfgce1 == (cfgld1 & ~motorenaint));
  assert property (cfgce2 == (cfgld2 & ~motorenaint));
  assert property (wdogdivregce == (wdogdivld & ~motorenaint));
  assert property (motorenaint |-> (!cfgce0 && !cfgce1 && !cfgce2 && !wdogdivregce));

  // Watchdog count clock select
  assert property (wdogcntce == (tst ? ce64 : ce16384));

  // Bitfield mappings
  assert property (invphase0  == configreg0[5]);
  assert property (invertpwm0 == configreg0[4]);
  assert property (invphase1  == configreg1[5]);
  assert property (invertpwm1 == configreg1[4]);
  assert property (invphase2  == configreg2[5]);
  assert property (invertpwm2 == configreg2[4]);

  // Coverage: exercise both watchdog clock paths
  cover property (tst && (wdogcntce == ce64));
  cover property (!tst && (wdogcntce == ce16384));
endmodule
bind control control_sva control_sva_i();