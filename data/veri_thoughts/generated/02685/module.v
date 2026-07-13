module xnor_xor (
  input [2:0] in1,
  input [2:0] in2,
  input [1:0] in3,
  output out1,
  output out2
);

  wire [2:0] xnor_out;
  assign xnor_out = ~(in1 ^ in2);
  
  assign out1 = xnor_out[2] & xnor_out[1] & xnor_out[0];
  assign out2 = out1 ^ in3[1];

endmodule
