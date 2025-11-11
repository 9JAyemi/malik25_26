// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  count
);

  // past_valid to safely use $past(...)
  logic past_valid;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Reset behavior: clears now-or-next event, and holds zero while asserted
  property p_reset_clears_now_or_next;
    @(posedge reset or posedge clk) $rose(reset) |-> ##[0:1] (count == 4'd0);
  endproperty
  assert property (p_reset_clears_now_or_next);

  assert property (@(posedge clk) reset |-> (count == 4'd0));

  // No X/Z on count when out of reset
  assert property (@(posedge clk) !reset |-> !$isunknown(count));

  // Hold behavior when enable=0
  assert property (@(posedge clk) disable iff (reset)
                   !enable |=> $stable(count));

  // Increment by 1 (mod-16) when enable=1
  assert property (@(posedge clk) disable iff (reset)
                   past_valid && enable |=> count == ($past(count) + 4'd1));

  // Any change of count must be due to prior enable=1
  assert property (@(posedge clk) disable iff (reset)
                   past_valid && (count != $past(count)) |-> $past(enable));

  // Simple safety: count is always within 4-bit range (and known)
  assert property (@(posedge clk) !reset |-> (! $isunknown(count) && (int'(count) inside {[0:15]})));

  // Coverage

  // See a wrap from F -> 0 with enable
  cover property (@(posedge clk) disable iff (reset)
                  past_valid && ($past(count)==4'hF) && $past(enable) ##1 (count==4'h0));

  // See a hold cycle (enable=0, count stable)
  cover property (@(posedge clk) disable iff (reset)
                  !enable && $stable(count));

  // See back-to-back increments
  cover property (@(posedge clk) disable iff (reset)
                  enable [*3]);

  // See reset pulse and release
  cover property (@(posedge reset or posedge clk)
                  $rose(reset) ##1 !reset);

endmodule

// Bind SVA to DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (.*);