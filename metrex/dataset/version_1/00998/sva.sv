// SVA for binary_counter
module binary_counter_sva (
  input logic       clock,
  input logic       reset,
  input logic [3:0] count
);

  default clocking cb @(posedge clock); endclocking

  // Sanity: no X/Z on key signals at sample time
  a_reset_known: assert property (!$isunknown(reset));
  a_count_known: assert property (!$isunknown(count));

  // Reset behavior: next cycle is 0, and holds at 0 while reset stays asserted
  a_reset_clears_next: assert property (reset |=> count == 4'd0);
  a_reset_holds_zero:  assert property ((reset && $past(reset)) |-> count == 4'd0);

  // Functional behavior: when running (no reset now or in prior cycle), increment by 1 mod-16
  a_incr_when_running: assert property ((!reset && !$past(reset)) |-> count == ($past(count) + 4'd1));

  // Coverage
  c_reset_effect: cover property (reset ##1 (count == 4'd0));
  c_wrap:         cover property ((!reset && !$past(reset) && ($past(count) == 4'hF)) |-> (count == 4'h0));
  sequence inc_step;
    (!reset && !$past(reset) && (count == ($past(count) + 4'd1)));
  endsequence
  c_16_steps:     cover property (inc_step [*16]);

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva sva_i (.clock(clock), .reset(reset), .count(count));