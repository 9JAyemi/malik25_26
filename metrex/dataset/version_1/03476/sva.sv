// SVA for sync_counter
module sync_counter_sva (
  input clk,
  input reset,
  input enable,
  input [3:0] out
);

  // Synchronous reset drives 0 on following clock
  property p_sync_reset_zero;
    @(posedge clk) reset |=> (out == 4'h0);
  endproperty
  assert property (p_sync_reset_zero);

  // When enabled (and not in reset), count increments mod-16
  property p_inc_when_enable;
    @(posedge clk) disable iff (reset)
      enable |=> (out == ($past(out) + 4'd1)[3:0]);
  endproperty
  assert property (p_inc_when_enable);

  // No spurious updates: out changes only if previously enabled
  property p_change_only_if_enable;
    @(posedge clk) disable iff (reset)
      $changed(out) |-> $past(enable);
  endproperty
  assert property (p_change_only_if_enable);

  // Out is known (no X/Z) after a reset has been seen
  property p_out_known_post_reset;
    @(posedge clk) disable iff (reset || !$past(reset))
      !$isunknown(out);
  endproperty
  assert property (p_out_known_post_reset);

  // Coverage
  // Reset pulse observed
  cover property (@(posedge clk) reset ##1 !reset);
  // Wrap-around when enabled at 0xF
  cover property (@(posedge clk) disable iff (reset)
                  (out == 4'hF && enable) |=> (out == 4'h0));
  // Hold behavior when disabled
  cover property (@(posedge clk) disable iff (reset)
                  !enable ##1 (out == $past(out)));

endmodule

bind sync_counter sync_counter_sva sva_i (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .out(out)
);