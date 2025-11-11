// SVA for up_counter
module up_counter_sva (
  input logic       clk,
  input logic       rst,
  input logic       en,
  input logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on inputs; output not X when out of reset
  assert property (!$isunknown({rst,en}));
  assert property (!rst |-> !$isunknown(count));

  // Reset behavior: synchronous reset forces 0
  assert property (rst |-> (count == 4'd0));

  // Functional behavior
  assert property (disable iff (rst) en  |-> count == $past(count) + 4'd1); // increment (wraps naturally)
  assert property (disable iff (rst) !en |-> count == $past(count));        // hold when disabled
  assert property (disable iff (rst) (count != $past(count)) |-> $past(en)); // changes only when en was 1

  // Coverage
  cover property ($rose(rst));
  cover property ($fell(rst));
  cover property (disable iff (rst) en && (count == 4'hF) ##1 (count == 4'h0)); // wrap-around
  cover property (disable iff (rst) !en ##1 $stable(count));                    // hold case
  cover property ($fell(rst) ##1 en ##1 (count == 4'd1));                        // first post-reset increment
endmodule

bind up_counter up_counter_sva u_sva(.clk(clk), .rst(rst), .en(en), .count(count));