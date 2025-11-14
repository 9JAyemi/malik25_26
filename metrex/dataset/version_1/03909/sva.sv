// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        rst,   // active-low
  input logic [3:0]  out
);

  // Sanity: no X/Z on key signals at clock
  assert property (@(posedge clk) !$isunknown(rst));
  assert property (@(posedge clk) !$isunknown(out));

  // Async reset takes effect immediately on negedge rst
  assert property (@(negedge rst) ##0 (out == 4'h0 && !$isunknown(out)));

  // While in reset, output is held at 0 on all clocks
  assert property (@(posedge clk) !rst |-> out == 4'h0);

  // First clock after reset release produces 1 (0 + 1)
  assert property (@(posedge clk) $rose(rst) |-> out == 4'h1);

  // Free-running count: increment by 1 each cycle when out of reset
  assert property (@(posedge clk) disable iff (!rst)
                   $past(rst) |-> out == $past(out) + 4'h1);

  // Coverage: reset pulse observed
  cover property (@(posedge clk) !rst ##1 rst);

  // Coverage: observe wrap-around F -> 0 while running
  cover property (@(posedge clk) disable iff (!rst)
                  out == 4'hF ##1 out == 4'h0);

  // Coverage: a few consecutive counts after release
  cover property (@(posedge clk) $rose(rst) ##1
                  out == 4'h1 ##1 out == 4'h2 ##1 out == 4'h3);
endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (.clk(clk), .rst(rst), .out(out));