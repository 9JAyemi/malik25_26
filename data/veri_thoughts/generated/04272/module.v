
module adder4bit (A, B, Ci, S, Co);
  input [3:0] A, B;
  input Ci;
  output [3:0] S;
  output Co;

  wire [3:0] c;
  wire [3:0] x;
  wire [3:0] y;

  // Full adder for the least significant bit
  full_adder FA0 (.a(A[0]), .b(B[0]), .ci(Ci), .s(S[0]), .co(c[0]));

  // Full adders for the remaining bits
  genvar i;
  generate
    for (i = 1; i < 4; i = i + 1) begin
      full_adder FA (.a(A[i]), .b(B[i]), .ci(c[i-1]), .s(S[i]), .co(c[i]));
    end
  endgenerate

  // Invert carry out to get Co
  assign Co = ~c[3];

  // Invert B to get 2's complement
  assign y = ~B;
  assign y[0] = y[0] ^ 1'b1;

  // Add inverted B to A
  full_adder FA1 (.a(A[0]), .b(y[0]), .ci(Ci), .s(x[0]), .co());
  generate
    for (i = 1; i < 4; i = i + 1) begin
      full_adder FA (.a(A[i]), .b(y[i]), .ci(c[i-1]), .s(x[i]), .co());
    end
  endgenerate
endmodule
module full_adder (a, b, ci, s, co);
  input a, b, ci;
  output s, co;

  wire x1, x2, x3;

  // First XOR gate
  assign x1 = a ^ b;

  // Second XOR gate
  assign s = x1 ^ ci;

  // AND gate
  assign x2 = a & b;

  // Third XOR gate
  assign x3 = x1 & ci;

  // OR gate
  assign co = x2 | x3;
endmodule