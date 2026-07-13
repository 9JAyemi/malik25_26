module adder_4bit(
  input [3:0] A,
  input [3:0] B,
  output [3:0] S,
  output C_out
);

  wire [3:0] sum;
  wire [3:0] carry;

  // Full Adders
  full_adder fa0(
    .a(A[0]),
    .b(B[0]),
    .c_in(1'b0),
    .sum(sum[0]),
    .c_out(carry[0])
  );

  full_adder fa1(
    .a(A[1]),
    .b(B[1]),
    .c_in(carry[0]),
    .sum(sum[1]),
    .c_out(carry[1])
  );

  full_adder fa2(
    .a(A[2]),
    .b(B[2]),
    .c_in(carry[1]),
    .sum(sum[2]),
    .c_out(carry[2])
  );

  full_adder fa3(
    .a(A[3]),
    .b(B[3]),
    .c_in(carry[2]),
    .sum(sum[3]),
    .c_out(C_out)
  );

  assign S = sum;

endmodule

module full_adder(
  input a,
  input b,
  input c_in,
  output sum,
  output c_out
);

  assign sum = a ^ b ^ c_in;
  assign c_out = (a & b) | (a & c_in) | (b & c_in);

endmodule