module adder_4bit ( A, B, Ci, S, Co );
  input [3:0] A, B;
  input Ci;
  output [3:0] S;
  output Co;

  wire [3:0] sum;
  wire c1, c2, c3;

  // Full-adder for least significant bit
  full_adder fa1(.a(A[0]), .b(B[0]), .c(Ci), .sum(sum[0]), .cout(c1));

  // Full-adder for second least significant bit
  full_adder fa2(.a(A[1]), .b(B[1]), .c(c1), .sum(sum[1]), .cout(c2));

  // Full-adder for third least significant bit
  full_adder fa3(.a(A[2]), .b(B[2]), .c(c2), .sum(sum[2]), .cout(c3));

  // Full-adder for most significant bit
  full_adder fa4(.a(A[3]), .b(B[3]), .c(c3), .sum(sum[3]), .cout(Co));

  assign S = sum;

endmodule

module full_adder (a, b, c, sum, cout);
  input a, b, c;
  output sum, cout;

  wire s1, c1, c2;

  // First half-adder
  half_adder ha1(.a(a), .b(b), .sum(s1), .cout(c1));

  // Second half-adder
  half_adder ha2(.a(s1), .b(c), .sum(sum), .cout(c2));

  // OR gate for carry-out
  assign cout = c1 | c2;

endmodule

module half_adder (a, b, sum, cout);
  input a, b;
  output sum, cout;

  // XOR gate for sum
  assign sum = a ^ b;

  // AND gate for carry-out
  assign cout = a & b;

endmodule