module full_adder(A, B, Cin, Sum, Cout);
    input A, B, Cin;
    output Sum, Cout;

    assign Sum = A ^ B ^ Cin;
    assign Cout = (A & B) | (B & Cin) | (A & Cin);
endmodule

module add4_carry(A, B, Cin, Sum, Cout);
    input [3:0] A, B;
    input Cin;
    output [3:0] Sum;
    output Cout;

    wire [3:0] S;
    wire C1, C2, C3;

    full_adder FA1(A[0], B[0], Cin, S[0], C1);
    full_adder FA2(A[1], B[1], C1, S[1], C2);
    full_adder FA3(A[2], B[2], C2, S[2], C3);
    full_adder FA4(A[3], B[3], C3, S[3], Cout);

    assign Sum = S;
endmodule