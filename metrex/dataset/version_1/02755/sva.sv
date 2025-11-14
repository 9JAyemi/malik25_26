// SVA for mux2to1
// Focus: async reset behavior, functional correctness, no glitches, X checks, and coverage.

`ifndef MUX2TO1_SVA
`define MUX2TO1_SVA

module mux2to1_sva (
  input logic A, B, sel, reset, clk,
  input logic out
);

  // Default synchronous assertions
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // Functional: out holds previous cycle's selected input (4-state aware: sel===0 -> A, else -> B)
  ap_func:            assert property (out == $past( (sel === 1'b0) ? A : B ));

  // Stability: if sel/A/B stable, out is stable
  ap_stable_inputs:   assert property ($stable(sel) && $stable(A) && $stable(B) |-> $stable(out));

  // No X on output when not in reset
  ap_no_x_out:        assert property (!$isunknown(out));

  // After reset deassertion, first active clock obeys function
  ap_after_rst_clk:   assert property (!$past(reset) && reset |-> out == $past( (sel === 1'b0) ? A : B ));

  // Out only changes on posedge clk or negedge reset (no glitches)
  ap_no_glitch_out:   assert property (disable iff (1'b0) $changed(out) |-> ($fell(reset) || $rose(clk)));

  // Async reset: immediate clear on falling edge and hold low while reset is low
  ap_async_clear:     assert property (@(negedge reset) ##0 (out == 1'b0));
  ap_hold_during_rst: assert property (@(posedge clk or negedge reset) !reset |-> (out == 1'b0 throughout !reset));

  // Coverage: exercise both data paths, reset edges, and output toggles
  cp_path_A:          cover property (sel === 1'b0 |=> out == $past(A));
  cp_path_B:          cover property (sel === 1'b1 |=> out == $past(B));
  cp_rst_fall:        cover property (@(negedge reset) 1);
  cp_rst_rise:        cover property (@(posedge  reset) 1);
  cp_out_rise:        cover property ($rose(out));
  cp_out_fall:        cover property ($fell(out));

endmodule

bind mux2to1 mux2to1_sva sva_mux2to1 (.*);

`endif