// SVA for counter_4bit
module counter_4bit_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] Q
);

  // Basic sanity: no X/Z at sample edges
  assert property (@(posedge clk) !$isunknown({clk,rst,Q}));

  // Async reset must clear immediately (post-NBA in same timestep)
  property async_rst_clears;
    @(posedge rst) 1 |-> ##0 (Q == 4'd0);
  endproperty
  assert property (async_rst_clears);

  // While reset held, Q is 0 at every clk edge
  assert property (@(posedge clk) rst |-> (Q == 4'd0));

  // First cycle after reset deasserts, Q increments from 0 to 1
  assert property (@(posedge clk) (!rst && $past(rst,1,1'b1)) |-> (Q == 4'd1));

  // Normal counting when not coming out of reset: Q == $past(Q) + 1 (mod 16)
  assert property (@(posedge clk) (!rst && !$past(rst,1,1'b1))
                   |-> (Q == $past(Q,1,4'd0) + 4'd1));

  // Explicit wrap check (redundant with the increment, but clearer)
  assert property (@(posedge clk) (!rst && !$past(rst,1,1'b1) && ($past(Q,1,4'd0) == 4'hF))
                   |-> (Q == 4'h0));

  // No mid-cycle glitches on Q except when async reset rises
  assert property (@(negedge clk) (!rst && !$rose(rst)) |-> $stable(Q));

  // Coverage
  cover property (@(posedge clk) rst ##1 !rst); // reset observed and released
  cover property (@(posedge clk) disable iff (rst) (Q == 4'hF) ##1 (Q == 4'h0)); // wrap
  cover property (@(posedge clk) disable iff (rst) (Q == $past(Q,1,4'd0) + 4'd1)); // normal step
  cover property (@(posedge rst) 1); // async reset event seen

endmodule

bind counter_4bit counter_4bit_sva sva (.clk(clk), .rst(rst), .Q(Q));