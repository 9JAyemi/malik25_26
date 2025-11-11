
module ripple_carry_adder (
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] S,
  output Cout
);

  wire [4:0] temp_S;  // Temporary output

  assign temp_S = A + B + Cin;

  assign S = temp_S[3:0];  // Assign the value of temp_S to S
  assign Cout = temp_S[4];  // Assign the carry out to Cout

endmodule
