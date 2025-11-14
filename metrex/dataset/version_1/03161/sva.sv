// SVA for binary_counter
module binary_counter_sva(input logic clk, rst, input logic [3:0] count);
  default clocking cb @(posedge clk); endclocking

  // Async reset clears immediately (after NBA) and holds while rst=1
  ap_async_clear:       assert property (@(posedge rst) ##0 (count == 4'd0));
  ap_hold_during_reset: assert property (rst |-> (count == 4'd0));

  // Increment by 1 modulo-16 on every clk when not in reset
  ap_inc_mod16:         assert property (disable iff (rst) (count == $past(count) + 4'd1));

  // First count after reset release is 1
  ap_first_after_rst:   assert property ($past(rst) && !rst |-> (count == 4'd1));

  // Count never X/Z at observed edges
  ap_no_xz:             assert property (!$isunknown(count));

  // Coverage
  cp_rst_assert:        cover property (@(posedge rst) 1);
  cp_rst_deassert:      cover property (@(negedge rst) 1);
  cp_one_inc:           cover property (!rst && (count == $past(count) + 4'd1));
  cp_wraparound:        cover property (!rst && ($past(count) == 4'hF) && (count == 4'h0));
  cp_first_is_1:        cover property ($past(rst) && !rst && (count == 4'd1));
endmodule

bind binary_counter binary_counter_sva u_sva(.clk(clk), .rst(rst), .count(count));