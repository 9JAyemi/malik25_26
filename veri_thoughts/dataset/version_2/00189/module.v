module full_adder (
    input A,
    input B,
    input Cin,
    output Sum,
    output Cout
);

    wire w1, w2, w3;

    assign w1 = A ^ B;
    assign Sum = w1 ^ Cin;
    assign w2 = A & B;
    assign w3 = w1 & Cin;
    assign Cout = w2 | w3;

endmodule

module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

    wire c1, c2, c3;

    full_adder FA0 (
        .A(A[0]),
        .B(B[0]),
        .Cin(Cin),
        .Sum(Sum[0]),
        .Cout(c1)
    );

    full_adder FA1 (
        .A(A[1]),
        .B(B[1]),
        .Cin(c1),
        .Sum(Sum[1]),
        .Cout(c2)
    );

    full_adder FA2 (
        .A(A[2]),
        .B(B[2]),
        .Cin(c2),
        .Sum(Sum[2]),
        .Cout(c3)
    );

    full_adder FA3 (
        .A(A[3]),
        .B(B[3]),
        .Cin(c3),
        .Sum(Sum[3]),
        .Cout(Cout)
    );

endmodule