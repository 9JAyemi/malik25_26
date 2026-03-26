module ripple_carry_adder(
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] S,
  output Cout
);

wire [3:0] sum;
wire [3:0] carry;

// full-adder for least significant bit
full_adder fa0(
  .A(A[0]),
  .B(B[0]),
  .Cin(Cin),
  .S(sum[0]),
  .Cout(carry[0])
);

// full-adder for second bit
full_adder fa1(
  .A(A[1]),
  .B(B[1]),
  .Cin(carry[0]),
  .S(sum[1]),
  .Cout(carry[1])
);

// full-adder for third bit
full_adder fa2(
  .A(A[2]),
  .B(B[2]),
  .Cin(carry[1]),
  .S(sum[2]),
  .Cout(carry[2])
);

// full-adder for most significant bit
full_adder fa3(
  .A(A[3]),
  .B(B[3]),
  .Cin(carry[2]),
  .S(sum[3]),
  .Cout(Cout)
);

assign S = sum;

endmodule


module full_adder(
  input A,
  input B,
  input Cin,
  output S,
  output Cout
);

assign {Cout, S} = A + B + Cin;

endmodule