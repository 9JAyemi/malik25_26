module ripple_carry_adder (
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] S,
  output Cout
);

wire [3:0] C;

// Full adder for the least significant bit
full_adder FA0(A[0], B[0], Cin, S[0], C[0]);

// Full adder for the remaining bits
full_adder FA1(A[1], B[1], C[0], S[1], C[1]);
full_adder FA2(A[2], B[2], C[1], S[2], C[2]);
full_adder FA3(A[3], B[3], C[2], S[3], Cout);

endmodule

module full_adder (
  input A,
  input B,
  input Cin,
  output S,
  output Cout
);

wire w1, w2, w3;

// XOR gate for sum
xor_gate XOR1(A, B, w1);
xor_gate XOR2(w1, Cin, S);

// AND gate for carry-out
and_gate AND1(A, B, w2);
and_gate AND2(w1, Cin, w3);
or_gate OR1(w2, w3, Cout);

endmodule

module xor_gate (
  input A,
  input B,
  output S
);

assign S = A ^ B;

endmodule

module and_gate (
  input A,
  input B,
  output S
);

assign S = A & B;

endmodule

module or_gate (
  input A,
  input B,
  output S
);

assign S = A | B;

endmodule