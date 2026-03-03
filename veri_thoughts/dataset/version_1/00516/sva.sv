// SVA for module counter
// Bind these assertions to the DUT

module counter_sva (
  input logic        clk,
  input logic        reset,   // active-low async
  input logic [3:0]  count
);

  // 1) Asynchronous reset must clear immediately at negedge (after NBA)
  property p_async_reset_clears;
    @(negedge reset) 1 |-> ##0 (count == 4'h0 && !$isunknown(count));
  endproperty
  assert property (p_async_reset_clears);

  // 2) While reset is held low, count must stay 0 on every clk
  property p_hold_zero_during_reset;
    @(posedge clk) !reset |-> (count == 4'h0 && !$isunknown(count));
  endproperty
  assert property (p_hold_zero_during_reset);

  // 3) When reset is high for two consecutive clocks, counter increments by 1 (mod 16)
  property p_inc_when_enabled;
    @(posedge clk) ($past(reset) && reset) |-> (count == $past(count) + 4'd1);
  endproperty
  assert property (p_inc_when_enabled);

  // 4) Explicit wrap-around check F -> 0 on next clock when enabled
  property p_wrap_around;
    @(posedge clk) ($past(reset) && reset && $past(count) == 4'hF) |-> (count == 4'h0);
  endproperty
  assert property (p_wrap_around);

  // 5) No X/Z on count when operating (reset high)
  property p_no_x_when_operating;
    @(posedge clk) reset |-> !$isunknown(count);
  endproperty
  assert property (p_no_x_when_operating);

  // -------- Coverage --------
  // See an async reset pulse
  cover property (@(negedge reset) 1);
  cover property (@(posedge clk) $rose(reset));

  // See at least one enabled increment
  cover property (@(posedge clk) ($past(reset) && reset) && (count == $past(count) + 4'd1));

  // See wrap-around F -> 0 while enabled
  cover property (@(posedge clk) ($past(reset) && reset && $past(count) == 4'hF) && (count == 4'h0));

endmodule

// Bind into DUT
bind counter counter_sva u_counter_sva (.clk(clk), .reset(reset), .count(count));