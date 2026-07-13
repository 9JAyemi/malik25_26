module ripple_carry_adder(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output Cout
);
    wire [3:0] C;
    
    assign C[0] = 1'b0; // Initialize the carry-in to 0
    
    // Full adder for bit 0
    full_adder FA0(A[0], B[0], C[0], S[0], C[1]);
    
    // Full adder for bit 1
    full_adder FA1(A[1], B[1], C[1], S[1], C[2]);
    
    // Full adder for bit 2
    full_adder FA2(A[2], B[2], C[2], S[2], C[3]);
    
    // Full adder for bit 3
    full_adder FA3(A[3], B[3], C[3], S[3], Cout);
    
endmodule

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