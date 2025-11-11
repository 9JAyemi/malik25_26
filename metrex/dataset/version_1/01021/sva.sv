// SVA for counter_4bit
module counter_4bit_sva (
  input logic       clk,
  input logic       rst,   // active-low async reset
  input logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Async reset takes effect immediately
  assert property (@(negedge rst) ##0 (count == 4'h0));

  // While in reset, hold at 0 (checked on clock)
  assert property (!rst |-> (count == 4'h0));

  // No X/Z on count when reset is known
  assert property (disable iff ($isunknown(rst)) !$isunknown(count));

  // Count behavior when out of reset
  // Increment by 1 when not wrapping
  assert property (disable iff (!rst)
                   ($past(count) != 4'hF) |-> (count == $past(count) + 4'd1));

  // Wrap from F to 0
  assert property (disable iff (!rst)
                   ($past(count) == 4'hF) |-> (count == 4'h0));

  // Coverage
  // See async reset taking effect
  cover property (@(negedge rst) ##0 (count == 4'h0));

  // See wrap F -> 0
  cover property (disable iff (!rst) (count == 4'hF) ##1 (count == 4'h0));

  // See a full 16-count cycle (0 -> 0 after 16 clocks)
  cover property (disable iff (!rst) (count == 4'h0) ##16 (count == 4'h0));

endmodule

bind counter_4bit counter_4bit_sva sva_inst (.clk(clk), .rst(rst), .count(count));