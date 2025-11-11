// SVA for d_ff_async_reset
module d_ff_async_reset_sva (
  input logic clk,
  input logic reset,   // active-low
  input logic d,
  input logic q
);

  default clocking cb @(posedge clk); endclocking

  // Async reset dominates: on falling edge, q drives 0 immediately
  ap_rst_immediate: assert property (@(negedge reset) ##0 (q===1'b0));

  // While in reset, q stays at 0
  ap_rst_hold:      assert property (@(posedge clk) !reset |-> (q===1'b0 && $stable(q)));

  // After reset release, q remains 0 until the first posedge clk
  ap_hold_zero_until_clk: assert property (@(posedge clk) $rose(reset) |-> ($past(q)===1'b0));

  // First capture after reset release: q reflects d sampled at that first clk
  ap_first_capture: assert property (@(posedge clk) $rose(reset) |=> (q===$past(d)));

  // Normal operation: with reset high for >=1 cycle, q is previous d
  ap_pipeline:      assert property (@(posedge clk) reset && $past(reset) |-> (q===$past(d)));

  // No spurious glitching: stable d implies stable q (beyond first cycle out of reset)
  ap_stable_d_no_glitch: assert property (@(posedge clk)
                                          reset && $past(reset) && $stable(d) |-> $stable(q));

  // Sanity: no X on d or q when reset is high
  ap_no_x:          assert property (@(posedge clk) reset |-> !$isunknown({d,q}));

  // Coverage
  cp_reset_pulse:   cover property (@(posedge clk) $fell(reset) ##[1:$] $rose(reset));
  cp_cap0:          cover property (@(posedge clk) reset && $past(reset) && ($past(d)===1'b0) && (q===1'b0));
  cp_cap1:          cover property (@(posedge clk) reset && $past(reset) && ($past(d)===1'b1) && (q===1'b1));

endmodule

bind d_ff_async_reset d_ff_async_reset_sva i_dff_sva (.clk(clk), .reset(reset), .d(d), .q(q));