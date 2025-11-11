// SVA for eim_burstcnt
// Bind into DUT; concise checks + key coverage

module eim_burstcnt_sva;
  // inserted into eim_burstcnt scope via bind; can see internal regs
  default clocking cb @(posedge bclk); endclocking

  // gate $past() at time 0
  bit past_valid; initial past_valid = 0;
  always @(posedge bclk) past_valid <= 1;

  // 1) Pipeline registers capture inputs (one-cycle delayed)
  assert property (past_valid |-> bus_ad_r == $past(bus_ad));
  assert property (past_valid |-> bus_a_r  == $past(bus_a));
  assert property (past_valid |-> cs_r     == $past(cs));
  assert property (past_valid |-> rw_r     == $past(rw));
  assert property (past_valid |-> adv_r    == $past(adv));

  // 2) Activated set/clear protocol
  localparam [6:0] MATCH = 7'h4F;
  wire match_now_past = $past(cs_r && adv_r && {bus_a_r, bus_ad_r[15:12]} == MATCH);

  // Rising of activated must come only from match in prior cycle
  assert property (past_valid && $rose(activated) |-> match_now_past);
  // If prior-cycle match, activated must be high now
  assert property (past_valid && match_now_past |-> activated);
  // Falling of activated must come only from prior-cycle !cs_r
  assert property (past_valid && $fell(activated) |-> $past(!cs_r));
  // If prior-cycle !cs_r, activated must be low now
  assert property (past_valid && $past(!cs_r) |-> !activated);

  // 3) Burst counter and final count behavior
  // When previously active: increment burstcnt, hold finalcnt
  assert property (past_valid && $past(activated)
                   |-> (burstcnt == $past(burstcnt) + 16'h1) && (finalcnt == $past(finalcnt)));
  // When previously inactive: capture finalcnt, clear burstcnt
  assert property (past_valid && $past(!activated)
                   |-> (finalcnt == $past(burstcnt)) && (burstcnt == 16'h0));

  // 4) activated_d is a 1-cycle delay of activated
  assert property (past_valid |-> activated_d == $past(activated));

  // 5) measured_burst update protocol and value
  // Update only on (activated_d && !activated)
  assert property (past_valid && !(activated_d && !activated) |-> measured_burst == $past(measured_burst));
  // When update happens, value = finalcnt + 1 (based on prior-cycle finalcnt)
  assert property (past_valid && (activated_d && !activated) |-> measured_burst == $past(finalcnt) + 16'h1);

  // 6) Basic functional coverage
  cover property (past_valid && $rose(activated));
  cover property (past_valid && $fell(activated));
  cover property (past_valid && $rose(activated) ##[1:$] $fell(activated));
  cover property (past_valid && (activated_d && !activated)); // expected update event
endmodule

bind eim_burstcnt eim_burstcnt_sva sva_inst();