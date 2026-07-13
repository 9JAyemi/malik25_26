module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] sum;
    wire c1, c2, c3;

    FA fa0(.A(A[0]), .B(B[0]), .Cin(Cin), .S(sum[0]), .Cout(c1));
    FA fa1(.A(A[1]), .B(B[1]), .Cin(c1), .S(sum[1]), .Cout(c2));
    FA fa2(.A(A[2]), .B(B[2]), .Cin(c2), .S(sum[2]), .Cout(c3));
    FA fa3(.A(A[3]), .B(B[3]), .Cin(c3), .S(sum[3]), .Cout(Cout));

    assign S = sum;

endmodule

module FA(
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    assign S = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));

endmodule