// SVA checker for sync_counter
module sync_counter_sva #(parameter int WIDTH = 3)
(
  input logic                   clk,
  input logic                   rst,
  input logic [WIDTH-1:0]       count_out
);

  // Known/clean signals at clk sampling
  assert property (@(posedge clk) !$isunknown(rst));
  assert property (@(posedge clk) !$isunknown(count_out));

  // Asynchronous reset drives 0 immediately at rst posedge (##0 to avoid race)
  assert property (@(posedge rst) ##0 (count_out == '0));

  // While in reset, output is 0 at each clk edge
  assert property (@(posedge clk) rst |-> (count_out == '0));

  // If staying in reset across clk edges, output remains stable (0)
  assert property (@(posedge clk) $past(1'b1) && rst && $past(rst) |-> $stable(count_out));

  // First clk after reset deassertion -> count = 1
  assert property (@(posedge clk) $past(1'b1) && !rst && $past(rst) |-> (count_out == 'd1));

  // Normal counting: +1 mod 2^WIDTH when not in reset across consecutive clks
  assert property (@(posedge clk) $past(1'b1) && !rst && !$past(rst)
                   |-> count_out == $past(count_out) + 'd1);

  // Wrap-around cover: max -> 0 (no reset across clks)
  cover property (@(posedge clk) $past(1'b1) && !rst && !$past(rst) &&
                  ($past(count_out) == {WIDTH{1'b1}}) && (count_out == '0));

  // Full cycle cover (0..7..0 without reset for WIDTH=3)
  sequence full_cycle_3;
    count_out==3'd0 ##1 3'd1 ##1 3'd2 ##1 3'd3 ##1 3'd4 ##1 3'd5 ##1 3'd6 ##1 3'd7 ##1 3'd0;
  endsequence
  cover property (@(posedge clk) disable iff (rst) full_cycle_3);

  // Reset activity covers
  cover property (@(posedge clk) $rose(rst));
  cover property (@(posedge clk) $fell(rst));

endmodule

// Bind into DUT
bind sync_counter sync_counter_sva #(.WIDTH(3))
  sync_counter_sva_i (.clk(clk), .rst(rst), .count_out(count_out));