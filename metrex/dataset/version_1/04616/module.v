module ripple_adder_4bit(A, B, Cin, S, Cout);
  input [3:0] A, B;
  input Cin;
  output [3:0] S;
  output Cout;

  wire [3:0] C;
  wire [3:0] sum;

  // First full adder
  full_adder FA0(.a(A[0]), .b(B[0]), .cin(Cin), .sum(sum[0]), .cout(C[0]));

  // Second full adder
  full_adder FA1(.a(A[1]), .b(B[1]), .cin(C[0]), .sum(sum[1]), .cout(C[1]));

  // Third full adder
  full_adder FA2(.a(A[2]), .b(B[2]), .cin(C[1]), .sum(sum[2]), .cout(C[2]));

  // Fourth full adder
  full_adder FA3(.a(A[3]), .b(B[3]), .cin(C[2]), .sum(sum[3]), .cout(Cout));

  // Output wires
  assign S = sum;

endmodule

module full_adder(a, b, cin, sum, cout);
  input a, b, cin;
  output sum, cout;

  // Calculate sum
  xor(sum, a, b, cin);

  // Calculate carry out
  assign cout = (a & b) | (a & cin) | (b & cin);
endmodule