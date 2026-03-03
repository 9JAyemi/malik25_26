// SVA for up_down_counter
module up_down_counter_sva (
  input clk,
  input reset,
  input direction,
  input [3:0] count
);

  // Sample after NBA so we can compare next-state with current inputs
  default clocking cb @(posedge clk);
    input #1step reset, direction, count;
  endclocking

  // Track that at least one sample has occurred for safe $past usage
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Synchronous reset drives zero in the same cycle
  a_reset_zero: assert property (@cb reset |-> (count == 4'h0));

  // Next-state function (increment/decrement with wrap), out of reset
  a_next_state: assert property (@cb disable iff (reset)
    past_valid |-> count ==
      (direction
        ? (($past(count) == 4'hF) ? 4'h0 : $past(count) + 1)
        : (($past(count) == 4'h0) ? 4'hF : $past(count) - 1))
  );

  // Count must change every cycle out of reset
  a_change: assert property (@cb disable iff (reset) past_valid |-> (count != $past(count)));

  // No X/Z on output out of reset
  a_no_x: assert property (@cb disable iff (reset) !$isunknown(count));

  // Coverage
  c_wrap_up:   cover property (@cb disable iff (reset)  direction && ($past(count) == 4'hF) && (count == 4'h0));
  c_wrap_down: cover property (@cb disable iff (reset) !direction && ($past(count) == 4'h0) && (count == 4'hF));
  c_dir_up:    cover property (@cb disable iff (reset) $rose(direction));
  c_dir_down:  cover property (@cb disable iff (reset) $fell(direction));
  c_hit_zero:  cover property (@cb disable iff (reset) (count == 4'h0));
  c_hit_max:   cover property (@cb disable iff (reset) (count == 4'hF));

endmodule

// Bind into the DUT
bind up_down_counter up_down_counter_sva u_up_down_counter_sva (
  .clk(clk), .reset(reset), .direction(direction), .count(count)
);