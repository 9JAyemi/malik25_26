module pipeemreg_sva (
  input logic i_wreg,
  input logic i_m2reg,
  input logic i_wmem,
  input logic [31:0] i_alu,
  input logic [31:0] i_b,
  input logic [4:0] i_rn,
  input logic clk,
  input logic rst,
  input logic o_wreg,
  input logic o_m2reg,
  input logic o_wmem,
  input logic [31:0] o_alu,
  input logic [31:0] o_b,
  input logic [4:0] o_rn
);
  // Clock: clk (posedge). Reset: rst (active-high, synchronous). Sequential pipeline reg: pass-through when !rst, zeros when rst.

  ///// Reset behavior (previous cycle rst -> outputs zero this cycle) /////
  // If rst was HIGH last cycle, o_wreg is 0 this cycle.
  reset_prev_clears_o_wreg: assert property (
    @(posedge clk) $past(rst) |-> (o_wreg == 1'b0)
  );
  // If rst was HIGH last cycle, o_m2reg is 0 this cycle.
  reset_prev_clears_o_m2reg: assert property (
    @(posedge clk) $past(rst) |-> (o_m2reg == 1'b0)
  );
  // If rst was HIGH last cycle, o_wmem is 0 this cycle.
  reset_prev_clears_o_wmem: assert property (
    @(posedge clk) $past(rst) |-> (o_wmem == 1'b0)
  );
  // If rst was HIGH last cycle, o_alu is 0 this cycle.
  reset_prev_clears_o_alu: assert property (
    @(posedge clk) $past(rst) |-> (o_alu == 32'd0)
  );
  // If rst was HIGH last cycle, o_b is 0 this cycle.
  reset_prev_clears_o_b: assert property (
    @(posedge clk) $past(rst) |-> (o_b == 32'd0)
  );
  // If rst was HIGH last cycle, o_rn is 0 this cycle.
  reset_prev_clears_o_rn: assert property (
    @(posedge clk) $past(rst) |-> (o_rn == 5'd0)
  );

  ///// Transfer behavior (previous cycle !rst -> outputs follow previous inputs) /////
  // When not in reset previously, o_wreg equals previous i_wreg.
  transfer_o_wreg_follows_i: assert property (
    @(posedge clk) disable iff (rst) ($past(rst) == 1'b0) |-> (o_wreg == $past(i_wreg))
  );
  // When not in reset previously, o_m2reg equals previous i_m2reg.
  transfer_o_m2reg_follows_i: assert property (
    @(posedge clk) disable iff (rst) ($past(rst) == 1'b0) |-> (o_m2reg == $past(i_m2reg))
  );
  // When not in reset previously, o_wmem equals previous i_wmem.
  transfer_o_wmem_follows_i: assert property (
    @(posedge clk) disable iff (rst) ($past(rst) == 1'b0) |-> (o_wmem == $past(i_wmem))
  );
  // When not in reset previously, o_alu equals previous i_alu.
  transfer_o_alu_follows_i: assert property (
    @(posedge clk) disable iff (rst) ($past(rst) == 1'b0) |-> (o_alu == $past(i_alu))
  );
  // When not in reset previously, o_b equals previous i_b.
  transfer_o_b_follows_i: assert property (
    @(posedge clk) disable iff (rst) ($past(rst) == 1'b0) |-> (o_b == $past(i_b))
  );
  // When not in reset previously, o_rn equals previous i_rn.
  transfer_o_rn_follows_i: assert property (
    @(posedge clk) disable iff (rst) ($past(rst) == 1'b0) |-> (o_rn == $past(i_rn))
  );

endmodule