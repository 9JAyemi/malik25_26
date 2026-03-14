module adder4bit(
  input [3:0] A,
  input [3:0] B,
  input C_in,
  output [3:0] S,
  output C_out
);

  wire [4:0] temp;
  
  assign temp = A + B + C_in;
  assign S = temp[3:0];
  assign C_out = temp[4];
  
endmodule