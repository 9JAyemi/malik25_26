module binary_adder(
  input [3:0] A,
  input [3:0] B,
  output [3:0] S,
  output C_out
);

  wire [3:0] carry;
  
  wire [4:0] S_temp;
  assign S_temp = A + B;
  assign carry = (S_temp[4] == 1) ? 1 : 0;
  assign C_out = carry;
  assign S = S_temp[3:0];
  
endmodule