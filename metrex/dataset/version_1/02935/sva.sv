// SVA checker for fifo_write_ptr_inc
// Notes:
// - Properties reflect the actual RTL semantics (2-bit case items compared against a 3-bit case expression).
// - Use a testbench clock/reset to sample this purely combinational block.

module fifo_write_ptr_inc_sva (
  input logic              clk,
  input logic              rst_n,
  input logic              ge2_free,
  input logic              ge3_free,
  input logic [1:0]        input_tm_cnt,
  input logic [3:0]        fifo_wrptr_inc
);

  // Output known and in-range
  assert property (@(posedge clk)
    disable iff (!rst_n)
    !$isunknown({ge2_free, ge3_free, input_tm_cnt, fifo_wrptr_inc}) and
    (fifo_wrptr_inc inside {[4'd0:4'd3]}));

  // Functional equivalence to RTL (explicit 3-bit decode of {ge3_free,input_tm_cnt})
  assert property (@(posedge clk)
    disable iff (!rst_n or $isunknown({ge2_free, ge3_free, input_tm_cnt}))
    fifo_wrptr_inc ==
      ( (!ge3_free && (input_tm_cnt==2'b11)) ? 4'd3 :
        (!ge3_free && (input_tm_cnt==2'b10)) ? (ge2_free ? 4'd2 : 4'd1) :
        (!ge3_free && (input_tm_cnt==2'b01)) ? 4'd1 :
        4'd0 ));

  // With the given RTL, ge3_free high always forces 0 (due to sizing in the case statement)
  assert property (@(posedge clk)
    disable iff (!rst_n or $isunknown(ge3_free))
    ge3_free |-> (fifo_wrptr_inc==4'd0));

  // Functional coverage: each decode path and output values
  cover property (@(posedge clk) disable iff (!rst_n)
    (!ge3_free && input_tm_cnt==2'b11 && fifo_wrptr_inc==4'd3)); // case 3'b011

  cover property (@(posedge clk) disable iff (!rst_n)
    (!ge3_free && input_tm_cnt==2'b10 && ge2_free && fifo_wrptr_inc==4'd2)); // case 3'b010, ge2=1

  cover property (@(posedge clk) disable iff (!rst_n)
    (!ge3_free && input_tm_cnt==2'b10 && !ge2_free && fifo_wrptr_inc==4'd1)); // case 3'b010, ge2=0

  cover property (@(posedge clk) disable iff (!rst_n)
    (!ge3_free && input_tm_cnt==2'b01 && fifo_wrptr_inc==4'd1)); // case 3'b001

  // Default arm coverage when ge3_free==1 for all input_tm_cnt
  cover property (@(posedge clk) disable iff (!rst_n)
    (ge3_free && input_tm_cnt==2'b00 && fifo_wrptr_inc==4'd0));
  cover property (@(posedge clk) disable iff (!rst_n)
    (ge3_free && input_tm_cnt==2'b01 && fifo_wrptr_inc==4'd0));
  cover property (@(posedge clk) disable iff (!rst_n)
    (ge3_free && input_tm_cnt==2'b10 && fifo_wrptr_inc==4'd0));
  cover property (@(posedge clk) disable iff (!rst_n)
    (ge3_free && input_tm_cnt==2'b11 && fifo_wrptr_inc==4'd0));

  // Hit all output values
  cover property (@(posedge clk) disable iff (!rst_n) fifo_wrptr_inc==4'd0);
  cover property (@(posedge clk) disable iff (!rst_n) fifo_wrptr_inc==4'd1);
  cover property (@(posedge clk) disable iff (!rst_n) fifo_wrptr_inc==4'd2);
  cover property (@(posedge clk) disable iff (!rst_n) fifo_wrptr_inc==4'd3);

endmodule

// Example bind (adjust clk/rst to your environment):
// bind fifo_write_ptr_inc fifo_write_ptr_inc_sva u_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));