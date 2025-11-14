// SVA for the provided design. Bind these to the DUT.
// Focused, high-quality checks with essential coverage.


// ===================== up_down_counter assertions =====================
module sva_up_down_counter;
  default clocking cb @(posedge clk); endclocking

  // Async reset drives q to CNT_MIN immediately and holds while asserted
  assert property (@(posedge reset) q == CNT_MIN);
  assert property (reset |-> q == CNT_MIN);

  // Step behavior: modulo-16 up/down (skip the 1st cycle after reset)
  assert property (disable iff (reset || $past(reset))
                   q == $past(q) + (up_down ? 4'h1 : 4'hF));

  // Range (generic w.r.t. params)
  assert property (disable iff (reset) (q >= CNT_MIN && q <= CNT_MAX));

  // Coverage: reset, inc/dec, wrap-up, wrap-down
  cover property (@(posedge reset) 1);
  cover property (disable iff (reset) up_down && q == $past(q) + 4'h1);
  cover property (disable iff (reset) !up_down && q == $past(q) + 4'hF);
  cover property (disable iff (reset) up_down && $past(q)==CNT_MAX && q==CNT_MIN);
  cover property (disable iff (reset) !up_down && $past(q)==CNT_MIN && q==CNT_MAX);
endmodule

bind up_down_counter sva_up_down_counter u_sva_up_down_counter;


// ===================== transition_detector assertions =====================
module sva_transition_detector;
  default clocking cb @(posedge clk); endclocking

  // Reset values
  assert property (@(posedge reset) transition==1'b0 && q_prev==4'b0000);
  assert property (reset |-> transition==1'b0);

  // transition is exactly the change detector of q (skip 1st cycle after reset)
  assert property (disable iff (reset || $past(reset))
                   transition == (q != $past(q)));

  // Coverage: see a transition pulse
  cover property (disable iff (reset) transition);
endmodule

bind transition_detector sva_transition_detector u_sva_transition_detector;


// ===================== top-level integration and latch-gate checks =====================
module sva_top_module;
  default clocking cb @(posedge clk); endclocking

  // Connectivity checks
  assert property (detector.q == counter.q);
  assert property (and_gate.transition == detector.transition);
  assert property (q == and_gate.out);

  // System-level: transition reflects counter output change
  assert property (disable iff (reset || $past(reset))
                   transition == (cnt_out != $past(cnt_out)));

  // When transition is high, out mirrors cnt_out at the sample
  assert property (disable iff (reset) transition |-> (q == cnt_out));

  // Hold behavior: if transition low across cycles, q holds
  assert property (disable iff (reset || $past(reset))
                   !transition && !$past(transition) |-> q == $past(q));

  // Out changes are gated by transition (approximate in clocked domain)
  assert property (disable iff (reset || $past(reset))
                   $changed(q) |-> (transition || $past(transition)));

  // Coverage: observe gated update and stability
  cover property (disable iff (reset) transition && q == cnt_out);
  cover property (disable iff (reset) !transition && q == $past(q));
endmodule

bind top_module sva_top_module u_sva_top_module;