// SVA for up_counter
module up_counter_sva (
  input logic        clk,
  input logic        rst,
  input logic        en,
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior: next cycle after rst high -> count == 0
  assert property (rst |=> count == 4'd0);

  // While rst is held, count remains 0 (checked cycle-to-cycle)
  assert property (disable iff (!rst) 1'b1 |-> count == 4'd0);

  // Increment when enabled (mod-16 due to 4-bit sizing)
  assert property (disable iff (rst) en |=> count == $past(count) + 4'd1);

  // Hold when not enabled
  assert property (disable iff (rst) !en |=> count == $past(count));

  // No X/Z on controls and output (post-reset for count)
  assert property (!$isunknown({rst,en}));
  assert property (disable iff (rst) !$isunknown(count));

  // Coverage
  cover property (rst ##1 count == 4'd0);                                // reset takes effect
  cover property (disable iff (rst) (en && count == 4'hF) ##1 count == 4'h0); // wrap-around
  cover property (disable iff (rst) !en ##1 (!en && count == $past(count)));  // hold behavior

endmodule

bind up_counter up_counter_sva u_up_counter_sva (.*);