// SVA for up_down_counter
module up_down_counter_sva (
  input clk,
  input reset,
  input up_down,
  input enable,
  input [3:0] count
);

  // Basic sanity: no X on important signals when out of reset
  assert property (@(posedge clk) !reset |-> !$isunknown({enable, up_down, count}));

  // Asynchronous reset effect sampled on clk: hold zero while reset is high
  assert property (@(posedge clk) reset |-> (count == 4'h0));
  // Also the first cycle after reset goes high must be zero
  assert property (@(posedge clk) $rose(reset) |=> (count == 4'h0));

  // Hold when not enabled
  assert property (@(posedge clk) (!reset && !enable) |=> (count == $past(count)));

  // Change whenever enabled (counter always moves when enabled)
  assert property (@(posedge clk) (!reset && enable) |=> (count != $past(count)));

  // Count up (non-wrap)
  assert property (@(posedge clk)
    (!reset && enable && up_down && (count != 4'hF)) |=> (count == $past(count) + 1));

  // Count up wrap 0xF -> 0x0
  assert property (@(posedge clk)
    (!reset && enable && up_down && (count == 4'hF)) |=> (count == 4'h0));

  // Count down (non-wrap)
  assert property (@(posedge clk)
    (!reset && enable && !up_down && (count != 4'h0)) |=> (count == $past(count) - 1));

  // Count down wrap 0x0 -> 0xF
  assert property (@(posedge clk)
    (!reset && enable && !up_down && (count == 4'h0)) |=> (count == 4'hF));

  // Covers: exercise both directions, wraps, and hold
  cover property (@(posedge clk)
    !reset && enable && up_down && (count != 4'hF) ##1 (count == $past(count) + 1));
  cover property (@(posedge clk)
    !reset && enable && up_down && (count == 4'hF) ##1 (count == 4'h0));
  cover property (@(posedge clk)
    !reset && enable && !up_down && (count != 4'h0) ##1 (count == $past(count) - 1));
  cover property (@(posedge clk)
    !reset && enable && !up_down && (count == 4'h0) ##1 (count == 4'hF));
  cover property (@(posedge clk)
    !reset && !enable ##1 $stable(count));

endmodule

// Bind into DUT
bind up_down_counter up_down_counter_sva u_up_down_counter_sva (
  .clk(clk),
  .reset(reset),
  .up_down(up_down),
  .enable(enable),
  .count(count)
);