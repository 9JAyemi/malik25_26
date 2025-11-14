// SVA for binary_counter
module binary_counter_sva(
  input clk,
  input rst,
  input [3:0] count_out,
  input overflow
);
  default clocking cb @(posedge clk); endclocking

  // No X when out of reset
  assert property (!rst |-> !$isunknown({count_out, overflow}));

  // Synchronous reset behavior and priority
  assert property (rst |-> count_out == 4'h0 && overflow == 1'b0);
  assert property (rst && $past(rst) |-> count_out == 4'h0 && overflow == 1'b0);

  // Next-state function (normal count and wrap)
  assert property (!rst && $past(count_out) != 4'hF |-> count_out == $past(count_out) + 4'd1 && overflow == 1'b0);
  assert property (!rst && $past(count_out) == 4'hF |-> count_out == 4'h0 && overflow == 1'b1);

  // Overflow correctness and single-cycle pulse
  assert property (overflow |-> !rst && $past(count_out) == 4'hF && count_out == 4'h0);
  assert property (overflow |=> !overflow);

  // Coverage
  cover property (rst);
  cover property (!rst && $past(count_out) != 4'hF && count_out == $past(count_out) + 4'd1 && !overflow);
  cover property (overflow);
  cover property ($fell(rst) ##[1:20] overflow);  // wrap observed within 20 cycles after reset deassert

endmodule

bind binary_counter binary_counter_sva u_sva(
  .clk(clk),
  .rst(rst),
  .count_out(count_out),
  .overflow(overflow)
);