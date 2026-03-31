module simple_counter_sva (
  input logic clk,
  input logic rst,
  input logic en,
  input logic [31:0] count
);
  // Clock: clk posedge. Reset: rst synchronous active-high. Counter increments on en, holds otherwise.

  // Reset drives count to 0 on each asserted cycle.
  reset_forces_zero: assert property (
    @(posedge clk) rst |-> (count == 32'd0)
  );

  // When not in reset and en is LOW, count holds its previous value.
  hold_when_en_low: assert property (
    @(posedge clk) disable iff (rst) ($past(1'b1) && !en) |-> (count == $past(count))
  );

  // When not in reset and en is HIGH, count increments by 1.
  increment_when_en_high: assert property (
    @(posedge clk) disable iff (rst) ($past(1'b1) && en) |-> (count == $past(count) + 32'd1)
  );

  // In non-reset cycles, count can change only if en is HIGH.
  change_requires_en: assert property (
    @(posedge clk) disable iff (rst) ($past(1'b1) && $changed(count)) |-> en
  );

  // When en stays LOW for two consecutive non-reset cycles, count is unchanged across two cycles.
  two_cycle_hold_when_en_low: assert property (
    @(posedge clk) disable iff (rst)
      ($past(1'b1,2) && !en && !$past(en) && !$past(rst) && !$past(rst,2))
      |-> (count == $past(count,2))
  );

  // With en HIGH at max value, count wraps to 0 on next cycle.
  wrap_to_zero_on_max: assert property (
    @(posedge clk) disable iff (rst) ($past(1'b1) && en && ($past(count) == 32'hFFFF_FFFF)) |-> (count == 32'h0000_0000)
  );

  // If both rst and en are HIGH, reset dominates and count is 0.
  reset_dominates_enable: assert property (
    @(posedge clk) (rst && en) |-> (count == 32'd0)
  );

endmodule