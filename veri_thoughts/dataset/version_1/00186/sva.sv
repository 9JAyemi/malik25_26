// SVA for module counter
module counter_sva(input logic clk, input logic rst, input logic [3:0] count);

  // Asynchronous reset must clear immediately and hold at 0 while asserted
  a_async_rst_clears: assert property (@(posedge rst) 1 |-> ##0 (count == 4'd0));
  a_rst_hold_zero:    assert property (@(posedge clk) rst |-> (count == 4'd0));

  // After deasserting reset, first clock should produce 1
  a_post_deassert_one: assert property (@(posedge clk) $fell(rst) |-> (count == 4'd1));

  // When not in reset, counter increments by 1 mod-16 each cycle
  a_inc_mod16: assert property (@(posedge clk) disable iff (rst)
                                !$isunknown($past(count)) |-> (count == $past(count) + 4'd1));

  // Coverage
  c_async_rst_seen:     cover property (@(posedge rst) 1);
  c_deassert_to_one:    cover property (@(posedge clk) $fell(rst) && (count == 4'd1));
  c_normal_increment:   cover property (@(posedge clk) disable iff (rst) (count == $past(count) + 4'd1));
  c_wraparound_seen:    cover property (@(posedge clk) disable iff (rst)
                                        ($past(count) == 4'hF && count == 4'h0));

endmodule

// Bind to DUT
bind counter counter_sva counter_sva_i(.clk(clk), .rst(rst), .count(count));