module button_counter_sva (
  input logic clk,
  input logic button,
  input logic [2:0] count
);

  // When button is high and count<5, next count increments by 1.
  check_increment_on_button_lt5: assert property (
    @(posedge clk) (button && (count < 3'd5)) |-> ##1 (count == $past(count) + 3'd1)
  );

  // When count is 5, next count becomes 0.
  check_wrap_to_zero_on_five: assert property (
    @(posedge clk) (count == 3'd5) |-> ##1 (count == 3'd0)
  );

  // Otherwise (not increment condition and not 5), count holds.
  check_hold_when_no_increment_conditions: assert property (
    @(posedge clk) ((! (button && (count < 3'd5))) && (count != 3'd5)) |-> ##1 (count == $past(count))
  );

  // If count is 4 and button is high, then 5 next and 0 the cycle after.
  check_two_cycle_4_button_to_0: assert property (
    @(posedge clk) (button && (count == 3'd4)) |-> ##1 (count == 3'd5) ##1 (count == 3'd0)
  );

  // If count > 5, it must hold its value.
  check_stable_when_gt5: assert property (
    @(posedge clk) (count > 3'd5) |-> ##1 (count == $past(count))
  );

  // If count changes to 0 from non-zero, previous count must have been 5.
  check_zero_must_follow_prev_five: assert property (
    @(posedge clk) 1'b1 |-> ##1 ( !((count == 3'd0) && ($past(count) != 3'd0)) || ($past(count) == 3'd5) )
  );

  // If count increases by 1, previous cycle had button high and count<5.
  check_increment_requires_button_and_lt5: assert property (
    @(posedge clk) 1'b1 |-> ##1 ( !(count == $past(count) + 3'd1) || ($past(button) && ($past(count) < 3'd5)) )
  );

  // Any decrement must be exactly 5 -> 0.
  check_only_decrement_is_5_to_0: assert property (
    @(posedge clk) 1'b1 |-> ##1 ( !(count < $past(count)) || ( ($past(count) == 3'd5) && (count == 3'd0) ) )
  );

  // Count cannot be 5 in two consecutive cycles.
  check_no_two_consecutive_five: assert property (
    @(posedge clk) (count == 3'd5) |-> ##1 (count != 3'd5)
  );

  // From prev <=5, next count cannot jump by more than +1.
  check_no_upskip_when_prev_le5: assert property (
    @(posedge clk) 1'b1 |-> ##1 ( !($past(count) <= 3'd5) || (count <= ($past(count) + 3'd1)) )
  );

endmodule