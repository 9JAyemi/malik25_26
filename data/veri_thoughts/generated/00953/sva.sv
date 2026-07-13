module up_down_counter_sva (
  input logic clk,
  input logic areset,
  input logic up_down,
  input logic load,
  input logic [3:0] load_value,
  input logic [3:0] count
);

  ///// Reset behavior /////
  // While reset is asserted (active-low), count must be 0.
  reset_holds_zero: assert property (
    @(posedge clk) (areset == 1'b0) |-> (count == 4'd0)
  );

  ///// Load behavior /////
  // When load is 1, next count equals current load_value.
  load_updates_count_next: assert property (
    @(posedge clk) disable iff (areset == 1'b0)
      (load == 1'b1) |=> (count == $past(load_value))
  );

  ///// Up/Down behavior /////
  // When load is 0 and up_down is 1, next count increments by 1 (mod 16).
  increment_update: assert property (
    @(posedge clk) disable iff (areset == 1'b0)
      (load == 1'b0 && up_down == 1'b1) |=> (count == ($past(count) + 4'd1))
  );

  // When load is 0 and up_down is 0, next count decrements by 1 (mod 16).
  decrement_update: assert property (
    @(posedge clk) disable iff (areset == 1'b0)
      (load == 1'b0 && up_down == 1'b0) |=> (count == ($past(count) - 4'd1))
  );

  ///// Wrap-around behavior /////
  // Increment wraps from 15 to 0.
  increment_wrap: assert property (
    @(posedge clk) disable iff (areset == 1'b0)
      (load == 1'b0 && up_down == 1'b1 && $past(count) == 4'hF) |=> (count == 4'h0)
  );

  // Decrement wraps from 0 to 15.
  decrement_wrap: assert property (
    @(posedge clk) disable iff (areset == 1'b0)
      (load == 1'b0 && up_down == 1'b0 && $past(count) == 4'h0) |=> (count == 4'hF)
  );

  ///// Sanity checks /////
  // When not loading, count must change each cycle by +/-1.
  change_when_no_load: assert property (
    @(posedge clk) disable iff (areset == 1'b0)
      (load == 1'b0) |=> (count != $past(count))
  );

  // Full next-state equation matches RTL priority and arithmetic.
  next_state_function: assert property (
    @(posedge clk) disable iff (areset == 1'b0)
      1'b1 |=> ( count == ( $past(load) ? $past(load_value)
                                : ( $past(up_down) ? ($past(count) + 4'd1)
                                                   : ($past(count) - 4'd1) ) ) )
  );

endmodule