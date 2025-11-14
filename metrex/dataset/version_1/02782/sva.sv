// SVA for binary_counter
module binary_counter_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Basic sanity: no X/Z on key signals after init
  assert property (!$isunknown(rst));
  assert property (!$isunknown(count));

  // Reset behavior: next-cycle 0 and hold 0 while asserted
  assert property (rst |=> count == 4'h0);
  assert property (rst && $past(rst) |-> count == 4'h0);
  // On reset deassertion edge, still observe 0 this cycle
  assert property ($fell(rst) |-> count == 4'h0);

  // Count increments by 1 (mod 16) when not in/reset in consecutive cycles
  assert property (!rst && !$past(rst) |-> count == ($past(count) + 4'd1));

  // Explicit wrap-around check
  assert property (!rst && !$past(rst) && $past(count) == 4'hF |-> count == 4'h0);

  // Functional coverage
  cover property (rst ##1 count == 4'h0);                               // reset forces 0
  cover property (!rst && !$past(rst) && $past(count)==4'h0 && count==4'h1); // normal inc
  cover property (!rst && !$past(rst) && $past(count)==4'hF && count==4'h0); // wrap
endmodule

bind binary_counter binary_counter_sva sva_i (.clk(clk), .rst(rst), .count(count));