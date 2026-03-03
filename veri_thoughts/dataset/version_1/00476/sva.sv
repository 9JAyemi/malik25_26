// SVA for counter
module counter_sva(input logic clk, rst, input logic [3:0] count);
  default clocking @(posedge clk); endclocking

  // Reset behavior
  a_async_reset:      assert property (@(posedge rst) count == 4'd0);
  a_sync_reset_hold:  assert property (rst |-> count == 4'd0);

  // Next-state function (mod-16), tolerant to async reset asserting before next clk
  a_next_state_mod16: assert property (disable iff (rst)
                                       1 |=> (rst || count == (($past(count)==4'hF) ? 4'h0 : $past(count)+1)));

  // No X on key signals at clock edge
  a_no_x:             assert property (!$isunknown({rst, count}));

  // Coverage
  c_seen_reset:             cover property (@(posedge rst) 1);
  c_first_inc_after_reset:  cover property ($fell(rst) ##1 (count == 4'd1));
  c_normal_inc:             cover property (disable iff (rst)
                                            (count inside {[4'h0:4'hE]}) ##1 (count == $past(count)+1));
  c_wrap:                   cover property (disable iff (rst) (count == 4'hF) ##1 (count == 4'h0));
endmodule

bind counter counter_sva u_counter_sva(.clk(clk), .rst(rst), .count(count));