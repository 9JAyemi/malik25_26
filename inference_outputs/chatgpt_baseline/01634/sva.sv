module posManager_sva (
   input logic        clk,
   input logic [15:0] pos11,
   input logic [15:0] pos12,
   input logic [15:0] pos21,
   input logic [15:0] pos22,
   input logic [15:0] pos_diff_x,
   input logic [15:0] pos_diff_y,
   input logic [31:0] count_clk,
   input logic [1:0]  clear,
   input logic [0:0]  m1,
   input logic [0:0]  m2
);
   // Clock: clk (posedge). No explicit reset. Mixed logic: sequential counter, combinational diffs with clear gating.

   // count_clk must be 0 when clear is 2'b10 or 2'b11.
   check_count_zero_on_clear_hi: assert property (
      @(posedge clk) ((clear == 2'b10) || (clear == 2'b11)) |-> (count_clk == 32'd0)
   );

   // pos_diff_x must be 0 when clear is 2'b10 or 2'b11.
   check_posdiffx_zero_on_clear_hi: assert property (
      @(posedge clk) ((clear == 2'b10) || (clear == 2'b11)) |-> (pos_diff_x == 16'd0)
   );

   // pos_diff_y must be 0 when clear is 2'b10 or 2'b11.
   check_posdiffy_zero_on_clear_hi: assert property (
      @(posedge clk) ((clear == 2'b10) || (clear == 2'b11)) |-> (pos_diff_y == 16'd0)
   );

   // pos_diff_x equals pos11 - pos21 when clear is not 2'b10 or 2'b11.
   check_posdiffx_calc_when_active: assert property (
      @(posedge clk) !((clear == 2'b10) || (clear == 2'b11)) |-> (pos_diff_x == (pos11 - pos21))
   );

   // pos_diff_y equals pos12 - pos22 when clear is not 2'b10 or 2'b11.
   check_posdiffy_calc_when_active: assert property (
      @(posedge clk) !((clear == 2'b10) || (clear == 2'b11)) |-> (pos_diff_y == (pos12 - pos22))
   );

   // With two consecutive active cycles, count_clk increments by 1 each cycle.
   check_count_inc_on_two_active: assert property (
      @(posedge clk)
      ( !((clear == 2'b10) || (clear == 2'b11)) ##1 !((clear == 2'b10) || (clear == 2'b11)) )
      |-> (count_clk == $past(count_clk) + 32'd1)
   );

   // With three consecutive active cycles, count_clk increases by 2 over two cycles.
   check_count_inc_by_two_on_three_active: assert property (
      @(posedge clk)
      ( !((clear == 2'b10) || (clear == 2'b11)) ##1 !((clear == 2'b10) || (clear == 2'b11)) ##1 !((clear == 2'b10) || (clear == 2'b11)) )
      |-> (count_clk == $past(count_clk,2) + 32'd2)
   );

   // When clear goes from 2'b10/2'b11 to active, next count_clk must be 1.
   check_count_one_after_release: assert property (
      @(posedge clk)
      ( ((clear == 2'b10) || (clear == 2'b11)) ##1 !((clear == 2'b10) || (clear == 2'b11)) )
      |-> (count_clk == 32'd1)
   );

   // pos_diff_x remains stable if clear, pos11 and pos21 are stable.
   check_posdiffx_stable_on_input_stable: assert property (
      @(posedge clk) ($stable(clear) && $stable(pos11) && $stable(pos21)) |-> $stable(pos_diff_x)
   );

   // pos_diff_y remains stable if clear, pos12 and pos22 are stable.
   check_posdiffy_stable_on_input_stable: assert property (
      @(posedge clk) ($stable(clear) && $stable(pos12) && $stable(pos22)) |-> $stable(pos_diff_y)
   );

endmodule