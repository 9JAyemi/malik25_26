module adder4bit (
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] Sum,
  output Cout
);

  wire c1, c2, c3;
  
  full_adder fa0(.a(A[0]), .b(B[0]), .c(Cin), .s(Sum[0]), .co(c1));
  full_adder fa1(.a(A[1]), .b(B[1]), .c(c1), .s(Sum[1]), .co(c2));
  full_adder fa2(.a(A[2]), .b(B[2]), .c(c2), .s(Sum[2]), .co(c3));
  full_adder fa3(.a(A[3]), .b(B[3]), .c(c3), .s(Sum[3]), .co(Cout));

endmodule

module full_adder (
  input a,
  input b,
  input c,
  output s,
  output co
);

  assign s = a ^ b ^ c;
  assign co = (a & b) | (c & (a ^ b));

endmodule