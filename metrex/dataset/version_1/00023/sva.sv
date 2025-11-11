// SVA for counter_4bit
// Bind this module to the DUT: bind counter_4bit counter_4bit_sva i_sva(.clk(clk), .rst(rst), .count(count));

module counter_4bit_sva(input clk, input rst, input [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Sanity: count must never be X/Z at clock edges
  assert property ( !$isunknown(count) );

  // Async reset must drive count to 0 immediately on rst posedge
  assert property (@(posedge rst) count == 4'd0);

  // While reset is asserted, counter holds at 0 on every clk edge
  assert property ( rst |-> (count == 4'd0) );

  // When not in reset in consecutive cycles, counter increments by 1 (mod 16)
  assert property ( (!rst && !$past(rst)) |-> (count == $past(count) + 4'd1) );

  // No spurious count changes except on clk posedge or rst posedge
  assert property ( $changed(count) |-> ($rose(clk) || $rose(rst)) );

  // Optional explicit wrap check (redundant with increment check, but clearer)
  assert property ( (!rst && !$past(rst) && $past(count) == 4'hF) |-> (count == 4'h0) );

  // Coverage

  // See a wrap: ... 14 -> 15 -> 0 while not in reset
  cover property ( (!rst && count == 4'd14) ##1 (!rst && count == 4'd15) ##1 (!rst && count == 4'd0) );

  // See reset then first two increments: rst -> 0 -> 1 -> 2
  cover property ( rst ##1 (!rst && count == 4'd0) ##1 (!rst && count == 4'd1) ##1 (!rst && count == 4'd2) );

  // See rst deassert on a clock edge and immediate increment from 0 to 1
  cover property ( $fell(rst) ##0 (count == 4'd1) );

endmodule