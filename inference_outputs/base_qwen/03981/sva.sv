```systemverilog
module demux_3to8_sva (
  input logic CLK,
  input logic in,
  input logic sel2,
  input logic sel1,
  input logic sel0,
  output logic out0,
  output logic out1,
  output logic out2,
  output logic out3,
  output logic out4,
  output logic out5,
  output logic out6,
  output logic out7
);

  // Ensure only one output is high at a time
  property p_one_hot;
    @(posedge CLK) disable iff (!CLK) $onehot({out0, out1, out2, out3, out4, out5, out6, out7});
  endproperty
  assert property (p_one_hot) else $error("More than one output is high at the same time");

  // Ensure the correct output is selected based on the inputs
  property p_correct_output;
    @(posedge CLK) disable iff (!CLK) 
      (sel2 == 0 && sel1 == 0 && sel0 == 0) |-> out0 == in && {out1, out2, out3, out4, out5, out6, out7} == 7'b0000000
      |-> (sel2 == 0 && sel1 == 0 && sel0 == 1) |-> out1 == in && {out0, out2, out3, out4, out5, out6, out7} == 7'b0000000
      |-> (sel2 == 0 && sel1 == 1 && sel0 == 0) |-> out2 == in && {out0, out1, out3, out4, out5, out6, out7} == 7'b0000000
      |-> (sel2 == 0 && sel1 == 1 && sel0 == 1) |-> out3 == in && {out0, out1, out2, out4, out5, out6, out7} == 7'b0000000
      |-> (sel2 == 1 && sel1 == 0 && sel0 == 0) |-> out4 == in && {out0, out1, out2, out3, out5, out6, out7} == 7'b0000000
      |-> (sel2 == 1 && sel1 == 0 && sel0 == 1) |-> out5 == in && {out0, out1, out2, out3, out4, out6, out7} == 7'b0000000
      |-> (sel2 == 1 && sel1 == 1 && sel0 == 0) |-> out6 == in && {out0, out1, out2, out3, out4, out5, out7} == 7'b0000000
      |-> (sel2 == 1 && sel1 == 1 && sel0 == 1) |-> out7 == in && {out0, out1, out2, out3, out4, out5, out6} == 7'b0000000;
  endproperty
  assert property (p_correct_output) else $error("Incorrect output selected");

endmodule
```