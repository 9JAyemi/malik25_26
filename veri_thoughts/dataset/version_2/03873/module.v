module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] X;
    wire [3:0] C;

    full_adder fa0 (
        .A(A[0]),
        .B(B[0]),
        .Cin(Cin),
        .S(X[0]),
        .C(C[0])
    );
    full_adder fa1 (
        .A(A[1]),
        .B(B[1]),
        .Cin(C[0]),
        .S(X[1]),
        .C(C[1])
    );
    full_adder fa2 (
        .A(A[2]),
        .B(B[2]),
        .Cin(C[1]),
        .S(X[2]),
        .C(C[2])
    );
    full_adder fa3 (
        .A(A[3]),
        .B(B[3]),
        .Cin(C[2]),
        .S(X[3]),
        .C(Cout)
    );

    assign S = X;

endmodule

module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output C
);

    wire s1;
    wire c1;
    wire c2;

    xor (s1, A, B);
    xor (S, s1, Cin);
    and (c1, A, B);
    and (c2, s1, Cin);
    or (C, c1, c2);

endmodule