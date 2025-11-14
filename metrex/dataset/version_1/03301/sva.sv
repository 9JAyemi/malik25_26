// SVA for binary_counter
module binary_counter_sva(input logic clk, rst, input logic [3:0] count);
  default clocking cb @ (posedge clk); endclocking

  // Sanity: no X/Z on key signals
  assert property (! $isunknown({rst, count})) else $error("X/Z on rst/count");

  // Reset behavior
  assert property (rst |=> count == 4'h0);
  assert property ((!$initstate && $past(rst) && rst) |-> count == 4'h0); // holds at 0 while held in reset
  assert property ((!$initstate && $past(rst) && !rst) |-> count == 4'h1); // first cycle after release

  // Next-state function (increment with wrap) when not in/reset
  assert property ((!$initstate && !rst && !$past(rst))
                   |-> count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 4'h1)));

  // Coverage
  cover property (rst ##1 count == 4'h0);                                          // reset drives zero
  cover property (!rst && $past(!rst) && $past(count) == 4'hF && count == 4'h0);   // wrap
  cover property (!rst && $past(!rst) && $past(count) != 4'hF && count == $past(count) + 4'h1); // increment
endmodule

// Bind to DUT
bind binary_counter binary_counter_sva u_binary_counter_sva(.clk(clk), .rst(rst), .count(count));