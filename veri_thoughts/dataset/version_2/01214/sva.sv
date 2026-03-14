module simple_counter_sva (
  input logic clk,
  input logic rst_n,
  input logic en,
  input logic [3:0] count
);
  // Clock: clk; Reset: rst_n active-low, synchronous
  // Sequential counter: increments on clk when en=1; holds when en=0; wraps 15->0

  // During reset, count is 0.
  reset_value: assert property (
    @(posedge clk) !rst_n |-> (count == 4'b0000)
  );

  // When en=0 (no reset), count holds its value.
  hold_when_en_low: assert property (
    @(posedge clk) disable iff (!rst_n) (!en) |-> $stable(count)
  );

  // When en=1 (no reset), count updates by +1 with wrap at 15->0.
  update_on_en_high: assert property (
    @(posedge clk) disable iff (!rst_n)
      en |-> (count == (($past(count) == 4'hf) ? 4'h0 : ($past(count) + 1'b1)))
  );

  // Any change to count (no reset) requires en=1.
  change_requires_en: assert property (
    @(posedge clk) disable iff (!rst_n) (!$stable(count)) |-> en
  );

  // When en=1 (no reset), the value must change.
  update_changes_value: assert property (
    @(posedge clk) disable iff (!rst_n) en |-> (count != $past(count))
  );

  // If en=1 and the new value is 0 (no reset), the previous value was 15.
  wrap_from_15_only: assert property (
    @(posedge clk) disable iff (!rst_n) (en && (count == 4'h0)) |-> ($past(count) == 4'hf)
  );

  // On the cycle reset is asserted, count is driven to 0.
  sync_reset_effect: assert property (
    @(posedge clk) $fell(rst_n) |-> (count == 4'h0)
  );
endmodule