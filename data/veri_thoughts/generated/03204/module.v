module full_adder(
    input A,
    input B,
    input Cin,
    output Sum,
    output Cout
);

assign {Cout, Sum} = A + B + Cin;

endmodule

module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

wire [3:0] C;
full_adder fa0(A[0], B[0], Cin, S[0], C[0]);
full_adder fa1(A[1], B[1], C[0], S[1], C[1]);
full_adder fa2(A[2], B[2], C[1], S[2], C[2]);
full_adder fa3(A[3], B[3], C[2], S[3], Cout);

endmodule