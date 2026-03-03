// SVA for counter_4bit
module counter_4bit_sva(
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // RESET: synchronous and dominant
  a_reset_zero: assert property (reset |-> count == 4'h0);

  // Known output when not in reset
  a_known_count: assert property (disable iff (reset) !$isunknown(count));

  // Hold when disabled
  a_hold_when_disabled: assert property (disable iff (reset) !enable |=> $stable(count));

  // Increment by 1 (mod 16) when enabled
  a_inc_when_enabled: assert property (disable iff (reset) enable |=> count == ($past(count) + 4'd1));

  // Explicit wrap check from 0xF -> 0x0 on enable
  a_wrap: assert property (disable iff (reset) (enable && count == 4'hF) |=> count == 4'h0);

  // Change only allowed if enable or reset (converse check)
  a_no_spurious_change: assert property (disable iff (reset) $changed(count) |-> $past(enable));

  // Coverage
  c_reset_seen:         cover property (reset);
  c_first_inc:          cover property (disable iff (reset) enable |=> count == ($past(count) + 4'd1));
  c_hold_seq:           cover property (disable iff (reset) !enable [*3] ##1 $stable(count));
  c_wrap_seq:           cover property (disable iff (reset) (enable && count == 4'hF) |=> count == 4'h0);

endmodule

// Bind into DUT
bind counter_4bit counter_4bit_sva sva_i(.clk(clk), .reset(reset), .enable(enable), .count(count));