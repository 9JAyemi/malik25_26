// SVA for binary_counter
module binary_counter_sva (
  input clk,
  input rst,
  input enable,
  input [7:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_clears:       assert property (rst |=> (count == 8'h00));
  a_reset_holds_zero:   assert property (($past(rst,1,1'b0) && rst) |-> (count == 8'h00));

  // Functional behavior
  a_inc_when_enable:    assert property (disable iff (rst) enable |=> (count == $past(count) + 8'd1));
  a_hold_when_disabled: assert property (disable iff (rst) !enable |=> $stable(count));
  a_change_only_when_ok:assert property ((!$stable(count)) |-> (rst || $past(enable,1,1'b0)));
  a_no_x_when_active:   assert property (!rst |-> !$isunknown(count));

  // Coverage
  c_reset_seen:         cover  property (rst ##1 (count == 8'h00));
  c_hold_seen:          cover  property (disable iff (rst) !enable ##1 $stable(count));
  c_inc_seen:           cover  property (disable iff (rst) enable ##1 (count == $past(count) + 8'd1));
  c_wrap_seen:          cover  property (disable iff (rst)
                                         (count==8'hFE && enable) ##1
                                         (count==8'hFF && enable) ##1
                                         (count==8'h00));
endmodule

bind binary_counter binary_counter_sva sva_i (.clk(clk), .rst(rst), .enable(enable), .count(count));