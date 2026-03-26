module full_adder(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    assign S = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));

endmodule

module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output Cout
);

    wire [3:0] C;

    full_adder fa0(.A(A[0]), .B(B[0]), .Cin(1'b0), .S(S[0]), .Cout(C[0]));
    full_adder fa1(.A(A[1]), .B(B[1]), .Cin(C[0]), .S(S[1]), .Cout(C[1]));
    full_adder fa2(.A(A[2]), .B(B[2]), .Cin(C[1]), .S(S[2]), .Cout(C[2]));
    full_adder fa3(.A(A[3]), .B(B[3]), .Cin(C[2]), .S(S[3]), .Cout(Cout));

endmodule