module synchronous_counter_sva (
  input logic clk,
  input logic rst,
  input logic en,
  input logic [3:0] count
);
  ///// Reset behavior /////
  // Synchronous reset drives count to zero on the clock edge.
  check_reset_clears_count: assert property (
    @(posedge clk) rst |-> (count == 4'd0)
  );

  // While reset is held across cycles, count stays zero and stable.
  check_continuous_reset_holds_zero: assert property (
    @(posedge clk) (rst && $past(rst)) |-> (count == 4'd0 && $stable(count))
  );

  // On reset deassert with en=0, count remains zero in that cycle.
  check_deassert_reset_en0_keeps_zero: assert property (
    @(posedge clk) ($fell(rst) && (en == 1'b0)) |-> (count == 4'd0)
  );

  // On reset deassert with en=1, count becomes one in that cycle.
  check_deassert_reset_en1_sets_one: assert property (
    @(posedge clk) ($fell(rst) && (en == 1'b1)) |-> (count == 4'd1)
  );

  ///// Enable and increment semantics /////
  // With en=1 (and no reset), count increments by one on the next cycle.
  check_increment_when_en_high: assert property (
    @(posedge clk) disable iff (rst) (en == 1'b1) |=> (count == $past(count) + 4'd1)
  );

  // With en=0 (and no reset), count holds its value on the next cycle.
  check_hold_when_en_low: assert property (
    @(posedge clk) disable iff (rst) (en == 1'b0) |=> (count == $past(count))
  );

  // If en=1 at count==15, next count wraps to zero.
  check_wrap_on_max: assert property (
    @(posedge clk) disable iff (rst) (en && (count == 4'hF)) |=> (count == 4'd0)
  );

  // Any change in count (no reset) implies en=1 and step is exactly +1 (mod 16).
  check_change_requires_en_and_plus1: assert property (
    @(posedge clk) disable iff (rst) $changed(count) |-> (en && (count == $past(count) + 4'd1))
  );

  // Two consecutive cycles of en=1 advance count by two.
  check_two_consecutive_en_increments_by2: assert property (
    @(posedge clk) disable iff (rst) (en ##1 en) |=> (count == $past(count,2) + 4'd2)
  );

  // en=1 then en=0 over two cycles advances count by one total.
  check_en_then_hold_advances_by1: assert property (
    @(posedge clk) disable iff (rst) (en ##1 !en) |=> (count == $past(count,2) + 4'd1)
  );

  // Two consecutive cycles of en=0 cause no change over those two cycles.
  check_two_cycles_no_en_no_change: assert property (
    @(posedge clk) disable iff (rst) (!en ##1 !en) |=> (count == $past(count,2))
  );
endmodule