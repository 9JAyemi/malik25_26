// SVA for counter
// Bind these to the DUT; concise but covers reset, increment, wrap, and X-checks.

`ifndef SYNTHESIS
module counter_sva (input logic clk, reset, input logic [7:0] count);

  default clocking cb @(posedge clk); endclocking

  // X checks
  ap_no_x_reset: assert property (!$isunknown(reset));
  ap_no_x_count: assert property (!$isunknown(count));

  // Asynchronous reset must force 0 immediately
  ap_async_reset_immediate: assert property (@(posedge reset) count == 8'h00);

  // While reset is asserted, count must be 0 on every clk
  ap_reset_holds_zero: assert property (reset |-> count == 8'h00);

  // When out of reset on consecutive sampled cycles, count increments by 1 modulo 256
  ap_inc_mod1: assert property (disable iff (reset || $past(reset))
                                count == $past(count + 8'h01));

  // Explicit wrap check on consecutive out-of-reset cycles
  ap_wrap: assert property (disable iff (reset || $past(reset))
                            $past(count) == 8'hFF |-> count == 8'h00);

  // Coverage
  cp_reset_assert:  cover property (@(posedge reset) 1);
  cp_first_inc:     cover property ($fell(reset) ##1 count == 8'h01);
  cp_wrap_seen:     cover property (disable iff (reset) $past(count) == 8'hFF && count == 8'h00);
  cp_hit_midvalue:  cover property (disable iff (reset) count == 8'hAA);

endmodule

bind counter counter_sva counter_sva_i (.clk(clk), .reset(reset), .count(count));
`endif