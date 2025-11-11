// SVA for glitch_filter
// Bind this to the DUT. Focuses on functional correctness, safety, and key coverage.

module glitch_filter_sva #(
  parameter int glitch_duration = 10
) (
  input  logic                     clk,
  input  logic                     in,
  input  logic                     out,
  input  logic [glitch_duration-1:0] glitch_counter
);

  // Sampling and startup mask (no reset available)
  default clocking cb @(posedge clk); endclocking
  logic init_done;
  initial init_done = 1'b0;
  always @(posedge clk) init_done <= 1'b1;
  default disable iff (!init_done);

  // Basic sanity
  ap_no_x:       assert property ( !$isunknown({in,out,glitch_counter}) );
  ap_cnt_bounds: assert property ( unsigned'(glitch_counter) <= glitch_duration );

  // Precise next-state behavior (counter and out), referenced to $past (design updates occur after sampling)
  ap_cnt_up: assert property (
    $past(in) && (unsigned'($past(glitch_counter)) < glitch_duration)
    |-> glitch_counter == $past(glitch_counter) + 1 && $stable(out)
  );

  ap_cnt_saturate_and_set_out: assert property (
    $past(in) && (unsigned'($past(glitch_counter)) >= glitch_duration)
    |-> glitch_counter == '0 && out
  );

  ap_cnt_down: assert property (
    !$past(in) && (unsigned'($past(glitch_counter)) > 0)
    |-> glitch_counter == $past(glitch_counter) - 1 && $stable(out)
  );

  ap_out_low_when_zero_and_in_low: assert property (
    !$past(in) && (unsigned'($past(glitch_counter)) == 0)
    |-> !out && glitch_counter == 0
  );

  // Output transition causes (no spurious toggles)
  ap_rose_out_cause: assert property (
    $rose(out) |-> $past(in) && (unsigned'($past(glitch_counter)) >= glitch_duration)
  );

  ap_fell_out_cause: assert property (
    $fell(out) |-> !$past(in) && (unsigned'($past(glitch_counter)) == 0)
  );

  // Functional timing: long-high asserts, short-high filtered (from a low start)
  ap_rise_after_long_high: assert property (
    !out ##0 in[* (glitch_duration+1)] |-> out
  );

  ap_short_pulse_filtered: assert property (
    !out ##0 in[*1:glitch_duration] ##1 !in |-> !out
  );

  // Coverage
  cv_long_high_triggers: cover property ( in[* (glitch_duration+1)] ##0 $rose(out) );
  cv_short_glitch_filtered: cover property ( !out ##1 $rose(in) ##1 in[*1:glitch_duration] ##1 !in ##0 !out );
  cv_deassert_after_low: cover property ( out ##1 !in[*1:$] ##0 $fell(out) );

endmodule

// Bind into all instances of glitch_filter, including internal counter
bind glitch_filter glitch_filter_sva #(.glitch_duration(glitch_duration))
  u_glitch_filter_sva (.clk(clk), .in(in), .out(out), .glitch_counter(glitch_counter));