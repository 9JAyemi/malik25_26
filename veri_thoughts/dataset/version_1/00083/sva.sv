// SVA for binary_counter
module binary_counter_sva(
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Track past-valid to safely use $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: output must be known
  a_known_count: assert property (!$isunknown(count));

  // Reset dominates: when reset is 1 at a rising edge, count is 0 at that edge
  a_reset_zero: assert property (reset |-> count == 4'd0);

  // Hold when disabled (no reset): count must not change
  a_hold_when_disabled: assert property (past_valid && !reset && !enable |=> $stable(count));

  // Increment by 1 when enabled (no wrap case)
  a_inc_no_wrap: assert property (past_valid && !reset && enable && $past(count) != 4'hF
                                  |=> count == $past(count) + 4'd1);

  // Wrap from 15 to 0 when enabled
  a_wrap_on_max: assert property (past_valid && !reset && enable && $past(count) == 4'hF
                                  |=> count == 4'd0);

  // Any change must be caused by reset or enable
  a_change_has_cause: assert property (past_valid && (count != $past(count)) |-> (reset || enable));

  // Coverage
  c_reset_pulse:     cover property (past_valid && reset ##1 !reset);
  c_hold_sample:     cover property (past_valid && !reset && !enable ##1 $stable(count));
  c_inc_sample:      cover property (past_valid && !reset && enable && $past(count) != 4'hF
                                     |=> count == $past(count) + 4'd1);
  c_wrap_sample:     cover property (past_valid && !reset && enable && $past(count) == 4'hF
                                     |=> count == 4'd0);
  c_enable_run4:     cover property (past_valid && !reset ##1 (enable && !reset)[*4]);
endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva sva_inst (.*);