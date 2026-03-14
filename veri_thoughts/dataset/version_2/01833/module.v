module full_adder(A, B, Cin, S, Cout);
    input A, B, Cin;
    output S, Cout;
    
    assign S = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));
endmodule

module adder4(A, B, S, Cout);
    input [3:0] A, B;
    output [3:0] S;
    output Cout;
    
    wire C1, C2, C3;
    full_adder FA1(A[0], B[0], 1'b0, S[0], C1);
    full_adder FA2(A[1], B[1], C1, S[1], C2);
    full_adder FA3(A[2], B[2], C2, S[2], C3);
    full_adder FA4(A[3], B[3], C3, S[3], Cout);
endmodule