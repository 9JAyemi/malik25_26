module ripple_adder(A, B, CIN, S, COUT);
  input [3:0] A;
  input [3:0] B;
  input CIN;
  output [3:0] S;
  output COUT;

  wire [3:0] sum;
  wire [3:0] carry;

  // first full adder
  fulladder FA0(A[0], B[0], CIN, sum[0], carry[0]);

  // second full adder
  fulladder FA1(A[1], B[1], carry[0], sum[1], carry[1]);

  // third full adder
  fulladder FA2(A[2], B[2], carry[1], sum[2], carry[2]);

  // fourth full adder
  fulladder FA3(A[3], B[3], carry[2], sum[3], COUT);

  assign S = sum;

endmodule

module fulladder (a, b, ci, s, co);
  input a, b, ci;
  output co, s;

  wire d;

  assign d = a ^ b;
  assign s = d ^ ci;
  assign co = (b & ~d) | (d & ci);
endmodule