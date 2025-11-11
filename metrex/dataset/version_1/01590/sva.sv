// SVA for counter
// Bind into the DUT to observe internal in_prev
module counter_sva(
  input  logic       clk,
  input  logic       reset,
  input  logic       in,
  input  logic [7:0] count_out,
  input  logic       in_prev
);
  default clocking cb @ (posedge clk); endclocking

  // Async reset takes effect immediately
  ap_async_reset_immediate: assert property (@(posedge reset) ##0 (count_out==8'h00 && in_prev==1'b0));

  // While reset is 1, outputs are held at 0 on every clk
  ap_reset_hold:              assert property (reset |-> ##0 (count_out==8'h00 && in_prev==1'b0));

  // in_prev tracks prior-cycle in (excluding the cycle right after reset release)
  ap_inprev_tracks:           assert property ((!reset && !$past(reset)) |-> in_prev == $past(in));

  // Count increments by 1 on each rising edge of in (excluding cycles adjacent to reset)
  ap_inc_on_rise:             assert property ((!reset && !$past(reset) && $rose(in)) |-> count_out == $past(count_out) + 8'd1);

  // Explicit wrap check
  ap_wrap_on_ff:              assert property ((!reset && !$past(reset) && $rose(in) && $past(count_out)==8'hFF) |-> count_out==8'h00);

  // No change without a rising edge of in
  ap_no_change_no_rise:       assert property ((!reset && !$past(reset) && !$rose(in)) |-> count_out == $past(count_out));

  // Safety: at most one-step change per cycle when not near reset
  ap_step_bound:              assert property ((!reset && !$past(reset)) |-> (count_out == $past(count_out) || count_out == ($past(count_out)+8'd1)));

  // Known-value checks on observable state each clk
  ap_known:                   assert property (!$isunknown({count_out,in_prev}));

  // Coverage
  cp_reset_assert:    cover property (@(posedge reset) 1);
  cp_reset_release:   cover property ($fell(reset));
  cp_one_increment:   cover property ((!reset && !$past(reset) && $rose(in)) && (count_out == $past(count_out)+8'd1));
  cp_no_increment:    cover property (!reset && !$past(reset) && $stable(in) && (count_out == $past(count_out)));
  cp_wrap:            cover property (!reset && !$past(reset) && $rose(in) && $past(count_out)==8'hFF && count_out==8'h00);
endmodule

// Bind into the DUT
bind counter counter_sva u_counter_sva(.*);