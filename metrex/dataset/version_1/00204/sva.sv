// SVA for sync_module
// Bindable checker with concise, full functional coverage

module sync_module_sva (
  input  logic clk,
  input  logic in1,
  input  logic in2,
  input  logic out1,
  input  logic out2,
  input  logic in1_reg,
  input  logic in2_reg,
  input  logic out1_reg,
  input  logic out2_reg
);

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Pipeline equivalence (concise and complete)
  assert property ( {in1_reg, in2_reg} == $past({in1, in2}) )
    else $error("in*_reg must equal prior in*");

  assert property ( {out1_reg, out2_reg} == $past({in2_reg, in1_reg}) )
    else $error("out*_reg must equal prior swapped in*_reg");

  assert property ( {out1, out2} == $past({in2, in1}) )
    else $error("out* must equal prior swapped in*");

  // Cover propagation of both polarities through both paths
  cover property ( $rose(in1) ##1 $rose(out2) );
  cover property ( $fell(in1) ##1 $fell(out2) );
  cover property ( $rose(in2) ##1 $rose(out1) );
  cover property ( $fell(in2) ##1 $fell(out1) );
  // Simultaneous activity on both channels
  cover property ( ($rose(in1) && $rose(in2)) ##1 (out1 && out2) );

endmodule

bind sync_module sync_module_sva u_sync_module_sva (
  .clk     (clk),
  .in1     (in1),
  .in2     (in2),
  .out1    (out1),
  .out2    (out2),
  .in1_reg (in1_reg),
  .in2_reg (in2_reg),
  .out1_reg(out1_reg),
  .out2_reg(out2_reg)
);