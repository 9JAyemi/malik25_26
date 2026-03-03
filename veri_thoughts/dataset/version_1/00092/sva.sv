// SVA for up_down_counter
module up_down_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic        up_down,
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Synchronous reset: if reset is 1 on a clock, next cycle count must be 0
  a_sync_reset_next: assert property (reset |=> count == 4'h0);

  // All other properties disabled during reset
  default disable iff (reset);

  // No X on key signals (during active operation)
  a_no_x_count: assert property (!$isunknown(count));
  a_no_x_ctrl:  assert property (!$isunknown({enable, up_down}));

  // Hold when disabled
  a_hold_when_disabled: assert property (!enable |=> count == $past(count));

  // Enable causes a change (never hold when enabled)
  a_enable_changes: assert property (enable |=> count != $past(count));

  // Any change (not due to reset) must be because enable was 1
  a_change_requires_enable: assert property ((count != $past(count)) && !$past(reset) |-> $past(enable));

  // Up-counting (no wrap)
  a_up_incr: assert property (enable && up_down && count != 4'hF |=> count == $past(count) + 4'd1);
  // Up-counting (wrap 15 -> 0)
  a_up_wrap: assert property (enable && up_down && count == 4'hF |=> count == 4'h0);

  // Down-counting (no wrap)
  a_down_decr: assert property (enable && !up_down && count != 4'h0 |=> count == $past(count) - 4'd1);
  // Down-counting (wrap 0 -> 15)
  a_down_wrap: assert property (enable && !up_down && count == 4'h0 |=> count == 4'hF);

  // Coverage
  c_reset:         cover property (reset ##1 (count == 4'h0));
  c_hold:          cover property (!enable ##1 count == $past(count));
  c_up_step:       cover property (enable && up_down && count inside {[4'h0:4'hE]} ##1 count == $past(count) + 1);
  c_down_step:     cover property (enable && !up_down && count inside {[4'h1:4'hF]} ##1 count == $past(count) - 1);
  c_up_wrap:       cover property (enable && up_down && count == 4'hF ##1 count == 4'h0);
  c_down_wrap:     cover property (enable && !up_down && count == 4'h0 ##1 count == 4'hF);

endmodule

// Bind into DUT
bind up_down_counter up_down_counter_sva sva_i (
  .clk    (clk),
  .reset  (reset),
  .enable (enable),
  .up_down(up_down),
  .count  (count)
);