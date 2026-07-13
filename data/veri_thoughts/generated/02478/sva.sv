module sync_up_down_counter_sva (
  input logic clk,
  input logic up_down,
  input logic [2:0] q
);

  // Increment by 1 when up_down==0 and not wrapping
  check_inc_no_wrap: assert property (
    @(posedge clk) (up_down == 1'b0 && q != 3'd7) |=> (q == $past(q) + 3'd1)
  );

  // Wrap to 0 on increment from 7
  check_inc_wrap_to_zero: assert property (
    @(posedge clk) (up_down == 1'b0 && q == 3'd7) |=> (q == 3'd0)
  );

  // Decrement by 1 when up_down==1 and not wrapping
  check_dec_no_wrap: assert property (
    @(posedge clk) (up_down == 1'b1 && q != 3'd0) |=> (q == $past(q) - 3'd1)
  );

  // Wrap to 7 on decrement from 0
  check_dec_wrap_to_seven: assert property (
    @(posedge clk) (up_down == 1'b1 && q == 3'd0) |=> (q == 3'd7)
  );

  // Counter value changes every cycle
  check_always_moves: assert property (
    @(posedge clk) $past_valid |-> (q != $past(q))
  );

  // LSB toggles every cycle (±1 changes bit 0)
  check_lsb_toggles: assert property (
    @(posedge clk) $past_valid |-> (q[0] != $past(q[0]))
  );

  // After 8 consecutive increments, counter returns to start
  check_period_eight_up: assert property (
    @(posedge clk) (up_down == 1'b0)[*8] |=> (q == $past(q, 8))
  );

  // After 8 consecutive decrements, counter returns to start
  check_period_eight_down: assert property (
    @(posedge clk) (up_down == 1'b1)[*8] |=> (q == $past(q, 8))
  );

  // Increment then decrement over two cycles returns original value
  check_undo_inc_then_dec: assert property (
    @(posedge clk) (up_down == 1'b0) ##1 (up_down == 1'b1) |=> (q == $past(q, 2))
  );

  // Decrement then increment over two cycles returns original value
  check_undo_dec_then_inc: assert property (
    @(posedge clk) (up_down == 1'b1) ##1 (up_down == 1'b0) |=> (q == $past(q, 2))
  );

endmodule