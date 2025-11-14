// SVA for the design. Bind these into the DUT for verification.
// Focused, high-signal-quality checks with concise but complete coverage.

////////////////////////////////////////
// flip_flop assertions
////////////////////////////////////////
module flip_flop_sva();
  // Capture on negedge clk; async reset dominates
  // Reset drives q to 0 immediately on assertion
  ap_ff_async_rst_now: assert property (@(posedge reset) 1 |=> (q == 8'h00));
  // While reset remains asserted across negedges, q stays 0
  ap_ff_hold_rst:       assert property (@(negedge clk) (reset && $past(reset)) |-> (q == 8'h00));
  // On active edge without reset, q captures d
  ap_ff_cap:            assert property (@(negedge clk) !reset |=> (q == d));
  // No X/Z on q at sampling edges
  ap_ff_no_x:           assert property (@(negedge clk) !$isunknown(q));
  // Coverage
  cp_ff_reset:          cover  property (@(posedge reset) 1);
  cp_ff_first_cap:      cover  property (@(negedge clk) (!reset && $past(reset)) |=> (q == d));
endmodule
bind flip_flop flip_flop_sva ff_sva();


////////////////////////////////////////
// transition_detector assertions
////////////////////////////////////////
module transition_detector_sva();
  default clocking cb @(posedge clk); endclocking

  // Async reset clears state immediately
  ap_td_async_rst_now:  assert property (@(posedge reset) 1 |=> (out == 32'h0 && prev_in == 32'h0));
  // Synchronous paths: on clk with reset, clear after NBA
  ap_td_rst_clk:        assert property (cb reset |=> (out == 32'h0 && prev_in == 32'h0));
  // Functional update when not in reset: next-state equations
  ap_td_update:         assert property (cb !reset |=> (out == (in & ~prev_in)) && (prev_in == in));
  // Sanity: out is subset of in when not in reset
  ap_td_subset:         assert property (cb !reset |-> ((out & ~in) == 32'h0));
  // No X/Z on out at clk edges
  ap_td_no_x:           assert property (cb !$isunknown(out));
  // Coverage: detect at least one rising transition and first cycle after reset
  cp_td_edge:           cover  property (cb !reset && (out != 32'h0));
  cp_td_first_after_rst:cover  property (cb (!reset && $past(reset)) |=> (out == in && out != 32'h0));
endmodule
bind transition_detector transition_detector_sva td_sva();


////////////////////////////////////////
// bitwise_or assertions
////////////////////////////////////////
module bitwise_or_sva();
  // Pure combinational equivalence (use 3-state equality to avoid false X mismatches)
  ap_or_func:  assert property (@(*) (out === (in1 | in2[7:0])));
  // If inputs are known, output must be known
  ap_or_no_x:  assert property (@(*) (!$isunknown({in1, in2[7:0]})) |-> !$isunknown(out));
  // Coverage: see contribution from in2 path when in1 is zero
  cp_or_in2:   cover  property (@(*) (in1 == 8'h00) && (in2[7:0] != 8'h00) && (out == in2[7:0]));
endmodule
bind bitwise_or bitwise_or_sva bo_sva();


////////////////////////////////////////
// top_module integration assertions
////////////////////////////////////////
module top_module_sva();
  // Integration: q must be bitwise OR of sources at all times
  ap_top_or_bind: assert property (@(*) (q === (flip_flop_out | transition_out[7:0])));

  // Coverage: q change caused by transition_out with flip_flop_out stable
  cp_top_q_from_td: cover property (@(posedge clk)
                                    $changed(transition_out[7:0]) && !$changed(flip_flop_out) && $changed(q));
  // Coverage: q change caused by flip_flop_out with transition_out stable
  cp_top_q_from_ff: cover property (@(negedge clk)
                                    !$changed(transition_out[7:0]) && $changed(flip_flop_out) && $changed(q));
endmodule
bind top_module top_module_sva top_sva();