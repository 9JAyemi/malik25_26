module Ripple_Carry_Adder(
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] S,
  output Cout
);

  wire [3:0] sum;  //intermediate sum bits
  wire [3:0] carry;  //intermediate carry bits

  //full adder for least significant bit
  Full_Adder FA0 (
    .A(A[0]),
    .B(B[0]),
    .Cin(Cin),
    .S(sum[0]),
    .Cout(carry[0])
  );

  //full adder for second least significant bit
  Full_Adder FA1 (
    .A(A[1]),
    .B(B[1]),
    .Cin(carry[0]),
    .S(sum[1]),
    .Cout(carry[1])
  );

  //full adder for third least significant bit
  Full_Adder FA2 (
    .A(A[2]),
    .B(B[2]),
    .Cin(carry[1]),
    .S(sum[2]),
    .Cout(carry[2])
  );

  //full adder for most significant bit
  Full_Adder FA3 (
    .A(A[3]),
    .B(B[3]),
    .Cin(carry[2]),
    .S(sum[3]),
    .Cout(Cout)
  );

  assign S = sum;  //output sum bits

endmodule

//full adder module
module Full_Adder(
  input A,
  input B,
  input Cin,
  output S,
  output Cout
);

  assign S = A ^ B ^ Cin;  //XOR of inputs
  assign Cout = (A & B) | (Cin & (A ^ B));  //OR of ANDs

endmodule