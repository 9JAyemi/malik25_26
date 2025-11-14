// SVA for counter_3bit
module counter_3bit_sva (
  input logic       clk,
  input logic       reset,   // active-low
  input logic       enable,
  input logic [2:0] count
);

  // Sanity: no X on reset; no X on enable/count when active
  a_no_x_reset:        assert property (@(posedge clk) !$isunknown(reset));
  a_no_x_when_active:  assert property (@(posedge clk) reset |-> !$isunknown({enable,count}));

  // Async reset clears immediately (delta-cycle after negedge reset)
  a_async_clear:       assert property (@(negedge reset) 1 |-> ##0 (count == 3'd0));

  // While in reset, count is held at zero
  a_hold_zero_in_reset: assert property (@(posedge clk) !reset |-> count == 3'd0);

  // Functional step behavior (guard against just-exited reset)
  a_incr_when_en:      assert property (@(posedge clk) disable iff (!reset)
                                        $past(reset) && enable |-> count == ($past(count) + 3'd1));
  a_hold_when_dis:     assert property (@(posedge clk) disable iff (!reset)
                                        $past(reset) && !enable |-> count == $past(count));

  // Tighten: when active, only hold or +1 (mod 8)
  a_only_inc_or_hold:  assert property (@(posedge clk) disable iff (!reset)
                                        $past(reset) |-> (count == $past(count) ||
                                                          count == ($past(count) + 3'd1)));

  // Coverage
  // See all count values while active
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : CVAL
      c_val: cover property (@(posedge clk) disable iff (!reset) count == i[2:0]);
    end
  endgenerate

  // See an increment, a hold, and wrap-around 7->0
  c_incr: cover property (@(posedge clk) disable iff (!reset)
                          $past(reset) && enable ##1 count == ($past(count) + 3'd1));
  c_hold: cover property (@(posedge clk) disable iff (!reset)
                          $past(reset) && !enable ##1 count == $past(count));
  c_wrap: cover property (@(posedge clk) disable iff (!reset)
                          $past(reset) && $past(count) == 3'd7 && enable ##1 count == 3'd0);

  // See async clear event
  c_async_clear: cover property (@(negedge reset) ##0 count == 3'd0);

endmodule

bind counter_3bit counter_3bit_sva sva (.*);