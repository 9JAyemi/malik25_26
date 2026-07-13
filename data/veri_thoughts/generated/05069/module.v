module FourBitAdder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

   wire [3:0] C;

   // Instantiate four FullAdder modules for each bit
   FullAdder FA0 (A[0], B[0], Cin, S[0], C[0]);
   FullAdder FA1 (A[1], B[1], C[0], S[1], C[1]);
   FullAdder FA2 (A[2], B[2], C[1], S[2], C[2]);
   FullAdder FA3 (A[3], B[3], C[2], S[3], Cout);

endmodule

module FullAdder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    // Sum is the XOR of the three inputs
    assign S = A ^ B ^ Cin;

    // Carry-out is the majority function of the three inputs (AB + BCin + ACin)
    assign Cout = (A & B) | (B & Cin) | (A & Cin);

endmodule
