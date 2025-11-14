// SVA for burst_counter
// Bindable checker; references DUT internals directly
module burst_counter_sva;
  default clocking cb @(posedge bclk); endclocking

  logic init;
  initial init = 1'b0;
  always @(posedge bclk) init <= 1'b1;

  // Input sampling registers capture previous-cycle inputs
  assert property (disable iff (!init) bus_ad_r == $past(bus_ad));
  assert property (disable iff (!init) bus_a_r  == $past(bus_a));
  assert property (disable iff (!init) cs_r     == $past(cs));
  assert property (disable iff (!init) rw_r     == $past(rw));
  assert property (disable iff (!init) adv_r    == $past(adv));

  // activated_d is delayed activated
  assert property (disable iff (!init) activated_d == $past(activated));

  // Activation control (set/clear/hold)
  assert property (disable iff (!init)
    $past(cs_r && adv_r && ({bus_a_r, bus_ad_r[15:12]} == 7'h4F)) |-> activated);
  assert property (disable iff (!init) $past(!cs_r) |-> !activated);
  assert property (disable iff (!init)
    $past(cs_r && !(adv_r && ({bus_a_r, bus_ad_r[15:12]} == 7'h4F))) |-> activated == $past(activated));

  // Burst counter and finalcnt behavior
  assert property (disable iff (!init)
    !$past(activated) |-> (burstcnt == 16'h0 && finalcnt == $past(burstcnt)));
  assert property (disable iff (!init)
    $past(activated)  |-> (burstcnt == $past(burstcnt) + 16'h1 && finalcnt == $past(finalcnt)));

  // measured_burst updates only on detected falling edge (as coded) and with correct value
  assert property (disable iff (!init)
    (measured_burst != $past(measured_burst)) |-> $past(activated_d && !activated));
  assert property (disable iff (!init)
    $past(activated_d && !activated) |-> measured_burst == $past(finalcnt) + 16'h1);
  assert property (disable iff (!init)
    !$past(activated_d && !activated) |-> measured_burst == $past(measured_burst));

  // Simple functional coverage
  cover property (disable iff (!init)
    cs_r && adv_r && ({bus_a_r, bus_ad_r[15:12]} == 7'h4F));            // activation qualifier seen
  cover property (disable iff (!init)
    activated ##1 activated ##1 activated ##1 !activated);              // multi-cycle active then deassert
  cover property (disable iff (!init)
    $past(activated_d && !activated) ##1 (measured_burst == $past(finalcnt) + 16'h1)); // measured update event
endmodule

bind burst_counter burst_counter_sva bcnt_sva();