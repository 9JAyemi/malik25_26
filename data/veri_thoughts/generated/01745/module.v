module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output Cout
);

wire [3:0] C;

// Full adder for the least significant bit
full_adder fa0(A[0], B[0], 1'b0, S[0], C[0]);

// Full adder for the second least significant bit
full_adder fa1(A[1], B[1], C[0], S[1], C[1]);

// Full adder for the third least significant bit
full_adder fa2(A[2], B[2], C[1], S[2], C[2]);

// Full adder for the most significant bit
full_adder fa3(A[3], B[3], C[2], S[3], Cout);

endmodule

// Full adder module
module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

assign S = A ^ B ^ Cin;
assign Cout = (A & B) | (A & Cin) | (B & Cin);

endmodule