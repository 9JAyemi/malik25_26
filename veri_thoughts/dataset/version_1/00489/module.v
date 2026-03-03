
module rippleCarryAdder(A, B, Cin, Sum, Cout);
    input [3:0] A;
    input [3:0] B;
    input Cin;
    output [3:0] Sum;
    output Cout;

    wire [3:0] C;
    wire [3:0] S;

    fullAdder FA0(A[0], B[0], Cin, S[0], C[0]);
    fullAdder FA1(A[1], B[1], C[0], S[1], C[1]);
    fullAdder FA2(A[2], B[2], C[1], S[2], C[2]);
    fullAdder FA3(A[3], B[3], C[2], S[3], Cout);

    assign Sum = S;

endmodule
module fullAdder(A, B, Cin, Sum, Cout);
    input A;
    input B;
    input Cin;
    output Sum;
    output Cout;

    assign Sum = A ^ B ^ Cin;
    assign Cout = (A & B) | (B & Cin) | (Cin & A);

endmodule