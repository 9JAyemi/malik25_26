// SVA for dff_8. Bind into the DUT; concise checks + targeted coverage.

module dff_8_sva #(parameter WIDTH=8)
(
  input        clk,
  input        reset,       // active-low async
  input  [WIDTH-1:0] d,
  input  [WIDTH-1:0] q
);

  // Reset behavior
  ap_async_reset_immediate: assert property (@(negedge reset) ##0 (q == '0));
  ap_hold_zero_during_reset: assert property (@(posedge clk or negedge reset) (!reset) |-> (q == '0));

  // Functional capture on clock when out of reset
  ap_capture_on_clk: assert property (@(posedge clk)
                                      reset && !$isunknown($past(d)) |-> (q == $past(d)));

  // q should not glitch between clocks when not in reset
  ap_stable_between_clks: assert property (@(negedge clk) reset |-> $stable(q));

  // Sanity/knownness
  ap_reset_known: assert property (@(posedge clk or negedge reset or posedge reset) !$isunknown(reset));
  ap_q_known_when_operating: assert property (@(posedge clk)
                                              reset && !$isunknown($past(d)) |-> !$isunknown(q));

  // Coverage
  cp_async_reset_seen:     cover property (@(negedge reset) ##0 (q == '0));
  cp_capture_nonzero:      cover property (@(posedge clk)
                                           reset && !$isunknown($past(d)) && ($past(d) != '0) && (q == $past(d)));
  cp_capture_all_ones:     cover property (@(posedge clk)
                                           reset && ($past(d) == '1) && (q == '1));

endmodule

bind dff_8 dff_8_sva #(.WIDTH(8)) dff_8_sva_i (.clk(clk), .reset(reset), .d(d), .q(q));