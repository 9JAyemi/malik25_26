// SVA for up_counter
module up_counter_sva(input logic clk, rst,
                      input logic [3:0] count,
                      input logic       overflow);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset takes effect immediately
  ap_async_reset: assert property (@(posedge rst) ##0 (count == 4'd0));

  // While reset held, count is 0 (check post-NBA state on each clk)
  ap_reset_hold:  assert property (@(posedge clk) rst |-> ##0 (count == 4'd0));

  // Next-state: increment or wrap (post-NBA), when not in reset
  ap_next_state:  assert property (@(posedge clk)
                                   disable iff (rst)
                                   ##0 count == (($past(count) == 4'hF) ? 4'd0 : $past(count)+4'd1));

  // Overflow matches count==15 after updates on clk or rst edges
  ap_overflow_match: assert property (@(posedge clk or posedge rst)
                                      ##0 (overflow == (count == 4'hF)));

  // No X/Z on key outputs after updates
  ap_no_xz: assert property (@(posedge clk or posedge rst)
                             ##0 !$isunknown({count, overflow}));

  // Coverage

  // See overflow asserted
  cv_overflow_seen: cover property (@(posedge clk) disable iff (rst)
                                    (count == 4'hF && overflow));

  // See wrap from F -> 0 across a clock
  cv_wrap: cover property (@(posedge clk) disable iff (rst)
                           ($past(count) == 4'hF && ##0 count == 4'd0));

  // Reset then first increment to 1
  cv_reset_then_inc: cover property (@(posedge clk)
                                     rst ##1 !rst ##1 count == 4'd1);

endmodule

bind up_counter up_counter_sva sva(.clk(clk), .rst(rst), .count(count), .overflow(overflow));