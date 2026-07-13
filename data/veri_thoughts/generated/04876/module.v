module full_adder(A, B, Cin, S, Cout);
    input A, B, Cin;
    output S, Cout;
    
    assign S = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));
endmodule

module ripple_carry_adder(A, B, Cin, S, Cout);
    input [3:0] A, B;
    input Cin;
    output [3:0] S;
    output Cout;
    
    wire [3:0] C;
    
    full_adder FA0(A[0], B[0], Cin, S[0], C[0]);
    full_adder FA1(A[1], B[1], C[0], S[1], C[1]);
    full_adder FA2(A[2], B[2], C[1], S[2], C[2]);
    full_adder FA3(A[3], B[3], C[2], S[3], Cout);
endmodule

module four_bit_adder(A, B, Cin, C, Cout);
    input [3:0] A, B;
    input Cin;
    output [3:0] C;
    output Cout;
    
    ripple_carry_adder RCA(A, B, Cin, C, Cout);
endmodule