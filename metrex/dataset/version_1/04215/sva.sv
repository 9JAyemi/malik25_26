// SVA checker for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  count
);

  // Track when we have a valid $past() sample in non-reset
  logic past_valid;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Async reset must clear immediately (after NBA in same time slot)
  assert property (@(posedge rst) ##0 (count == 4'h0))
    else $error("count not cleared to 0 on posedge rst");

  // While rst is high, clock edges must keep count at 0
  assert property (@(posedge clk) rst |-> (count == 4'h0))
    else $error("count not held at 0 while rst is high");

  // After reset deassertion, first clock must advance to 1
  assert property (@(posedge clk) $fell(rst) |-> (count == 4'h1))
    else $error("count not 1 on first clk after rst deassert");

  // Mod-16 increment on every clk when not in reset
  assert property (@(posedge clk) disable iff (rst)
                   past_valid |-> (count == (($past(count)==4'hF) ? 4'h0 : $past(count)+1)))
    else $error("count did not increment mod-16");

  // No X/Z on count when not in reset
  assert property (@(posedge clk) disable iff (rst) !$isunknown(count))
    else $error("count has X/Z while not in reset");

  // Coverage: see a wrap from F to 0
  cover property (@(posedge clk) disable iff (rst)
                  ($past(count)==4'hF && count==4'h0));

  // Coverage: reset pulse followed by counting 0->1->2
  cover property (@(posedge clk)
                  $fell(rst) ##1 (count==4'h1) ##1 (count==4'h2));

endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (.clk(clk), .rst(rst), .count(count));