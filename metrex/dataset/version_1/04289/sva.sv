// SVA for flow_led
// Bindable checker that references DUT internals (alarm, count)
module flow_led_sva #(parameter int LEN=5, NUM=5) (flow_led dut);

  // Sanity on params
  initial begin
    assert (LEN > 0) else $error("LEN must be > 0");
    assert (NUM > 0) else $error("NUM must be > 0");
  end

  default clocking cb @(posedge dut.sig_step); endclocking

  // Shorthands
  let active_now   = dut.power && !dut.sig_ring;
  let active_past  = $past(dut.power && !dut.sig_ring && dut.alarm);

  // Basic invariants
  // Power off forces all-zero state
  assert property ( !dut.power |-> (dut.alarm==0 && dut.count==0 && dut.alarm_light==0) );

  // Ring sets start state (same cycle)
  assert property ( dut.power && dut.sig_ring |-> (dut.alarm==1 && dut.count==0 && dut.alarm_light==1) );

  // When idle (powered, no ring, alarm=0), hold zeros
  assert property ( dut.power && !dut.sig_ring && dut.alarm==0 |-> (dut.count==0 && dut.alarm_light==0) );

  // alarm implies count range [0 .. LEN-1]
  assert property ( dut.alarm |-> (dut.count < LEN) );

  // If alarm=0 then count must be 0
  assert property ( dut.alarm==0 |-> dut.count==0 );

  // Onehot-or-zero pattern on alarm_light whenever powered
  assert property ( dut.power |-> $onehot0(dut.alarm_light) );

  // Progress step while active and not at terminal count: increment and shift/seed
  assert property (
    active_now && active_past && ($past(dut.count) < LEN-1)
    |-> ( dut.alarm
          && dut.count == $past(dut.count)+1
          && dut.alarm_light == ( ($past(dut.alarm_light)!=0) ? ($past(dut.alarm_light) << 1) : 1 ) )
  );

  // Terminal step (previous count==LEN-1) clears everything same cycle
  assert property (
    active_now && active_past && ($past(dut.count) == LEN-1)
    |-> (dut.count==0 && dut.alarm==0 && dut.alarm_light==0)
  );

  // While active and not terminal, alarm must stay asserted
  assert property (
    active_now && active_past && ($past(dut.count) < LEN-1) |-> dut.alarm
  );

  // No spurious changes when idle (powered, no ring, alarm=0)
  assert property (
    dut.power && !dut.sig_ring && dut.alarm==0 |-> $stable(dut.count) && $stable(dut.alarm_light)
  );

  // Coverage
  // 1) Ring -> run exactly LEN steps -> auto clear
  cover property (
    dut.power && dut.sig_ring
    ##1 (dut.power && !dut.sig_ring && dut.alarm)[*LEN]
    ##1 (!dut.alarm && dut.alarm_light==0 && dut.count==0)
  );

  // 2) Overflow wrap to zero during shift (onehot MSB shifts out) while still active
  cover property (
    active_now && active_past && ($past(dut.alarm_light[NUM-1])==1) && ($past(dut.count) < LEN-1)
    ##1 (dut.alarm && dut.alarm_light==0)
  );

  // 3) Ring restart during active alarm
  cover property ( $past(dut.alarm) && dut.power && dut.sig_ring );

  // 4) Power drop during active alarm
  cover property ( $past(dut.alarm) && !dut.power );

endmodule

// Bind into the DUT
bind flow_led flow_led_sva #(.LEN(LEN), .NUM(NUM)) flow_led_sva_i (.*);