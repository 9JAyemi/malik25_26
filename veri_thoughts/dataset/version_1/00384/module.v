module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    assign S = A ^ B ^ Cin;
    assign Cout = (A & B) | (Cin & (A ^ B));

endmodule


module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] S_int;
    wire C0, C1, C2;

    full_adder fa0 (
        .A(A[0]),
        .B(B[0]),
        .Cin(Cin),
        .S(S_int[0]),
        .Cout(C0)
    );

    full_adder fa1 (
        .A(A[1]),
        .B(B[1]),
        .Cin(C0),
        .S(S_int[1]),
        .Cout(C1)
    );

    full_adder fa2 (
        .A(A[2]),
        .B(B[2]),
        .Cin(C1),
        .S(S_int[2]),
        .Cout(C2)
    );

    full_adder fa3 (
        .A(A[3]),
        .B(B[3]),
        .Cin(C2),
        .S(S_int[3]),
        .Cout(Cout)
    );

    assign S = S_int;

endmodule