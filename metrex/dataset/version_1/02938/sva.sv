// SVA for fifo_counter
module fifo_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        up_count,
  input logic        down_count,
  input logic [2:0]  num_entries
);

  // Guard for $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // No X/Zs on key signals after first cycle
  assert_no_x: assert property (@(posedge clk) past_valid |-> !$isunknown({reset, up_count, down_count, num_entries}));

  // Synchronous reset: next cycle is zero; stays zero while held
  a_reset_next_zero: assert property (@(posedge clk) past_valid && $past(reset) |-> num_entries == 3'd0);

  // State update rule with priority (up over down)
  a_update_rule: assert property (@(posedge clk)
    past_valid && !$past(reset) |-> 
      num_entries ==
        ( $past(up_count)  ? ($past(num_entries) + 3'd1) :
          ($past(down_count)? ($past(num_entries) - 3'd1) :
                              $past(num_entries) ) )
  );

  // Explicit precedence check when both asserted -> increment
  a_both_inc: assert property (@(posedge clk)
    past_valid && !$past(reset) && $past(up_count) && $past(down_count)
    |-> num_entries == ($past(num_entries) + 3'd1)
  );

  // Hold when no enables
  a_hold: assert property (@(posedge clk)
    past_valid && !$past(reset) && !$past(up_count) && !$past(down_count)
    |-> num_entries == $past(num_entries)
  );

  // Output changes only on posedge clk (no mid-cycle glitches)
  a_no_glitch: assert property (@(negedge clk) $stable(num_entries));

  // ---------------------------------
  // Coverage
  // ---------------------------------

  // See a reset pulse
  c_reset: cover property (@(posedge clk) $rose(reset));

  // Increment event
  c_inc: cover property (@(posedge clk)
    past_valid && !$past(reset) && $past(up_count) && !$past(down_count)
    ##1 num_entries == $past(num_entries)+3'd1
  );

  // Decrement event
  c_dec: cover property (@(posedge clk)
    past_valid && !$past(reset) && !$past(up_count) && $past(down_count)
    ##1 num_entries == $past(num_entries)-3'd1
  );

  // Priority when both asserted
  c_both: cover property (@(posedge clk)
    past_valid && !$past(reset) && $past(up_count) && $past(down_count)
    ##1 num_entries == $past(num_entries)+3'd1
  );

  // Wrap-around up: 7 -> 0
  c_wrap_up: cover property (@(posedge clk)
    past_valid && !$past(reset) && ($past(num_entries)==3'd7) && $past(up_count) && !$past(down_count)
    ##1 (num_entries==3'd0)
  );

  // Wrap-around down: 0 -> 7
  c_wrap_down: cover property (@(posedge clk)
    past_valid && !$past(reset) && ($past(num_entries)==3'd0) && !$past(up_count) && $past(down_count)
    ##1 (num_entries==3'd7)
  );

  // Hold (no change)
  c_hold: cover property (@(posedge clk)
    past_valid && !$past(reset) && !$past(up_count) && !$past(down_count)
    ##1 num_entries == $past(num_entries)
  );

endmodule

// Bind to DUT
bind fifo_counter fifo_counter_sva u_fifo_counter_sva (
  .clk(clk),
  .reset(reset),
  .up_count(up_count),
  .down_count(down_count),
  .num_entries(num_entries)
);