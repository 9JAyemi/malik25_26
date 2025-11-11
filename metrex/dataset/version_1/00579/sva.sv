// SVA bind module for latch_MEM_WB
module latch_MEM_WB_sva
  #(parameter B=32, W=5)
  (
    input wire clk,
    input wire reset,
    input wire ena,

    input  wire [B-1:0] read_data_in,
    input  wire [B-1:0] alu_result_in,
    input  wire [W-1:0] mux_RegDst_in,

    output wire [B-1:0] read_data_out,
    output wire [B-1:0] alu_result_out,
    output wire [W-1:0] mux_RegDst_out,

    input  wire wb_RegWrite_in,
    input  wire wb_MemtoReg_in,

    output wire wb_RegWrite_out,
    output wire wb_MemtoReg_out
  );

  localparam int OUTW = 2*B + W + 2;

  wire [OUTW-1:0] outs = {read_data_out, alu_result_out, mux_RegDst_out, wb_RegWrite_out, wb_MemtoReg_out};
  wire [OUTW-1:0] ins  = {read_data_in,  alu_result_in,  mux_RegDst_in,  wb_RegWrite_in,  wb_MemtoReg_in};

  default clocking cb @(posedge clk); endclocking

  // Reset: clear on next cycle and hold zeros while reset is high
  assert property ($rose(reset) |=> (outs == '0));
  assert property ((reset && $past(reset)) |-> (outs == '0));

  // Enable=1: capture inputs on next cycle
  assert property ((!reset && (ena === 1'b1)) |=> (outs == $past(ins)));

  // Enable!=1: hold value (including ena=0 or X/Z)
  assert property ((!reset && !(ena === 1'b1)) |=> (outs == $past(outs)));

  // Any change must be due to previous reset or previous ena==1
  assert property ($past(1'b1) |-> ((outs != $past(outs)) |-> ($past(reset) || ($past(ena) === 1'b1))));

  // No X on outputs when not in reset
  assert property ($past(1'b1) |-> (!reset |-> !$isunknown(outs)));

  // Functional coverage
  cover property ($rose(reset) ##1 (outs == '0));
  cover property (!reset && (ena === 1'b1) ##1 (outs == $past(ins)));
  cover property (!reset && !(ena === 1'b1) ##1 (outs == $past(outs)));

  // Capture transitions on control bits
  cover property (!reset && (ena === 1'b1) && $changed(wb_RegWrite_in) ##1 (wb_RegWrite_out == $past(wb_RegWrite_in)));
  cover property (!reset && (ena === 1'b1) && $changed(wb_MemtoReg_in) ##1 (wb_MemtoReg_out == $past(wb_MemtoReg_in)));

  // Data path capture on change
  cover property (!reset && (ena === 1'b1) && (read_data_in  != $past(read_data_in))  ##1 (read_data_out  == $past(read_data_in)));
  cover property (!reset && (ena === 1'b1) && (alu_result_in != $past(alu_result_in)) ##1 (alu_result_out == $past(alu_result_in)));

  // Hold behavior even if inputs toggle while ena!=1
  cover property (!reset && !(ena === 1'b1) && (ins != $past(ins)) ##1 (outs == $past(outs)));

endmodule

// Bind into DUT
bind latch_MEM_WB latch_MEM_WB_sva #(.B(B), .W(W)) latch_MEM_WB_sva_i (.*);