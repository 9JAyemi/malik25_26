module mux4to1_sva (
  input logic clk,
  input logic rst_n,
  input logic in0,
  input logic in1,
  input logic in2,
  input logic in3,
  input logic sel0,
  input logic sel1,
  input logic out
);

  // Sequential logic assertions

  // Output should be one of the inputs based on the selection
  mux_output: assert property (
    @(posedge clk) disable iff (!rst_n) (out == (sel0 ? (sel1 ? in3 : in2) : (sel1 ? in1 : in0)))
  ) else $error("Output is not one of the inputs based on the selection");

  // Combinational logic assertions

  // Mux2to1 logic should be correct
  mux2to1_output: assert property (
    @(posedge clk) disable iff (!rst_n) (mux2to1_out == (sel0 ? in1 : in0))
  ) else $error("Mux2to1 output is incorrect");

  mux2to1_output2: assert property (
    @(posedge clk) disable iff (!rst_n) (mux2to1_out2 == (sel0 ? in3 : in2))
  ) else $error("Mux2to1 output is incorrect");

endmodule