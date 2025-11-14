// SVA for binary_counter
module binary_counter_sva (
  input logic        clock,
  input logic        reset,
  input logic [3:0]  counter_output
);
  default clocking cb @(posedge clock); endclocking

  // Guard to make $past safe
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clock) past_valid <= 1'b1;

  // Reset behavior: next cycle after any cycle with reset=1, counter is 0
  ap_reset_zero: assert property (reset |=> counter_output == 4'h0);

  // Increment by 1 mod-16 on every cycle with reset=0
  ap_inc_mod16: assert property (
    past_valid && !reset |=> counter_output == (($past(counter_output)+4'd1) & 4'hF)
  );

  // Explicit wrap check: F -> 0 when reset=0
  ap_wrap: assert property (
    past_valid && !reset && counter_output == 4'hF |=> counter_output == 4'h0
  );

  // Counter must be known (no X/Z) once reset has been observed
  ap_known_after_reset: assert property (
    past_valid && $past(reset) |-> !$isunknown(counter_output)
  );

  // Coverage
  // See a reset, then count 1,2,3
  cv_reset_then_count: cover property (
    reset ##1 !reset ##1 counter_output==4'h1 ##1 counter_output==4'h2 ##1 counter_output==4'h3
  );

  // See wrap-around F -> 0 with reset low
  cv_wrap: cover property (!reset && counter_output==4'hF ##1 counter_output==4'h0);
endmodule

// Bind into DUT
bind binary_counter binary_counter_sva sva_i (.*);