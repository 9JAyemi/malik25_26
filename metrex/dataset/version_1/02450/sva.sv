// SVA for up_counter
module up_counter_sva(
  input logic       clk,
  input logic       rst,   // active-low async
  input logic       en,
  input logic [3:0] count
);

  // Asynchronous reset correctness
  ap_async_reset: assert property (@(negedge rst) ##0 (count == 4'h0));
  ap_reset_hold:  assert property (@(posedge clk) (!rst) |-> (count == 4'h0));

  // X/Z checks
  ax_rst_known: assert property (@(posedge clk) !$isunknown(rst));
  ax_en_known:  assert property (@(posedge clk) disable iff (!rst) !$isunknown(en));
  ax_cnt_known: assert property (@(posedge clk) !$isunknown(count));

  // Functional behavior when not in reset
  ap_inc:  assert property (@(posedge clk) disable iff (!rst) en  |-> (count == $past(count) + 1));
  ap_hold: assert property (@(posedge clk) disable iff (!rst) !en |-> (count == $past(count)));
  ap_wrap: assert property (@(posedge clk) disable iff (!rst)
                            $past(en) && $past(count) == 4'hF |-> count == 4'h0);

  // Coverage
  cp_reset:    cover property (@(negedge rst) ##0 (count == 4'h0));
  cp_inc:      cover property (@(posedge clk) disable iff (!rst) (en && count == $past(count) + 1));
  cp_hold:     cover property (@(posedge clk) disable iff (!rst) (!en && count == $past(count)));
  cp_rollover: cover property (@(posedge clk) disable iff (!rst)
                               (count == 4'hE && en) ##1 (count == 4'hF && en) ##1 (count == 4'h0));
  cp_rst_en:   cover property (@(negedge rst) en);

endmodule

bind up_counter up_counter_sva sva(.clk(clk), .rst(rst), .en(en), .count(count));