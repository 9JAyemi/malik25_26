// SVA for counter_module
// Bind this file to the DUT: bind counter_module counter_module_sva cm_sva();

module counter_module_sva;

  // Access DUT scope directly via bind (no ports)
  // Signals: clk, reset, count, internal_count, max_count

  // Default sampling
  default clocking cb @(posedge clk); endclocking

  // Static parameter check
  initial assert (max_count <= 8'hFF)
    else $error("max_count exceeds 8-bit range");

  // 1) Output mirrors internal reg
  assert property (count == internal_count);

  // 2) No X/Z on output when not in reset
  assert property (disable iff (reset) !$isunknown(count));

  // 3) While reset is asserted, counter holds zero (continuously)
  assert property (reset |-> (internal_count == 8'd0 && count == 8'd0));

  // 4) Asynchronous reset takes effect immediately at reset edge
  assert property (@(posedge reset) internal_count == 8'd0);

  // 5) Next-state function: increment or wrap, when not in reset
  assert property (disable iff (reset)
    internal_count == (($past(internal_count) == max_count) ? 8'd0 : ($past(internal_count) + 8'd1)));

  // 6) Any zero observed in non-reset cycles must be a wrap-from-max (no spurious jumps to zero)
  assert property (disable iff (reset)
    (internal_count == 8'd0 && $past(reset) == 1'b0) |-> ($past(internal_count) == max_count));

  // 7) Count never goes X/Z in non-reset next-state computation window
  assert property (disable iff (reset)
    !$isunknown($past(internal_count)) && !$isunknown(internal_count));

  // Coverage

  // C1) See a wrap from max_count to 0
  cover property (disable iff (reset)
    ($past(internal_count) == max_count) && (internal_count == 8'd0));

  // C2) See at least three consecutive increments (no wrap)
  cover property (disable iff (reset)
    (internal_count == $past(internal_count) + 8'd1)[*3]);

  // C3) Asynchronous reset asserted mid-count (not at zero) and immediately clears to zero
  cover property (@(posedge reset)
    ($past(internal_count, 1, posedge clk) inside {[8'd1:max_count]}) && (internal_count == 8'd0));

  // C4) Reset release followed by first increment
  cover property (@(posedge clk)
    $fell(reset) ##1 (internal_count == 8'd0) ##1 (internal_count == 8'd1));

endmodule