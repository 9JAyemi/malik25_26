// SVA for up_down_counter
// Bind this module to the DUT for checks and coverage
module up_down_counter_sva #(parameter int W=9)
(
  input clk,
  input reset,
  input up_down,
  input enable,
  input [W-1:0] q
);

  default clocking cb @(posedge clk); endclocking

  // Async reset drives q to 0 immediately
  ap_async_reset: assert property (@(posedge reset) q == '0);

  // While reset is asserted, q must be 0 at every clk edge
  ap_reset_hold:  assert property (reset |-> (q == '0));

  // No X/Z on outputs/controls after reset
  ap_no_x:        assert property (disable iff (reset) !$isunknown({q, enable, up_down}));

  // Hold when disabled
  ap_hold_dis:    assert property (disable iff (reset) !enable |=> q == $past(q));

  // Count up exactly +1 modulo 2^W when enabled and up_down=1
  ap_count_up:    assert property (disable iff (reset)
                                   (enable && up_down) |=> q == ($past(q) + (W+1)'(1))[W-1:0]);

  // Count down exactly -1 modulo 2^W when enabled and up_down=0
  ap_count_dn:    assert property (disable iff (reset)
                                   (enable && !up_down) |=> q == ($past(q) - (W+1)'(1))[W-1:0]);

  // q may only change on clk because enable was 1 in the previous cycle (exclude reset)
  ap_only_when_en: assert property (disable iff (reset) $changed(q) |-> $past(enable));

  // Explicit wrap checks (concise, rely on past state)
  ap_wrap_up:     assert property (disable iff (reset)
                                   ($past(enable) && $past(up_down) && $past(q) == {W{1'b1}}) |-> (q == '0));
  ap_wrap_dn:     assert property (disable iff (reset)
                                   ($past(enable) && !$past(up_down) && $past(q) == '0) |-> (q == {W{1'b1}}));

  // Functional coverage
  cp_inc:         cover property (disable iff (reset) enable && up_down ##1 q == ($past(q)+(W+1)'(1))[W-1:0]);
  cp_dec:         cover property (disable iff (reset) enable && !up_down ##1 q == ($past(q)-(W+1)'(1))[W-1:0]);
  cp_hold:        cover property (disable iff (reset) !enable ##1 q == $past(q));
  cp_wrap_up:     cover property (disable iff (reset)
                                  $past(enable && up_down && q=={W{1'b1}}) ##1 (q=='0));
  cp_wrap_dn:     cover property (disable iff (reset)
                                  $past(enable && !up_down && q=='0) ##1 (q=={W{1'b1}}));

endmodule

// Bind to DUT
bind up_down_counter up_down_counter_sva #(.W(9)) u_sva (.*);