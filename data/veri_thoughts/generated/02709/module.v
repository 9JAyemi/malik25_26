module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C_out
);

    wire [3:0] C;

    full_adder fa0(
        .A(A[0]),
        .B(B[0]),
        .C_in(1'b0),
        .S(S[0]),
        .C_out(C[0])
    );

    full_adder fa1(
        .A(A[1]),
        .B(B[1]),
        .C_in(C[0]),
        .S(S[1]),
        .C_out(C[1])
    );

    full_adder fa2(
        .A(A[2]),
        .B(B[2]),
        .C_in(C[1]),
        .S(S[2]),
        .C_out(C[2])
    );

    full_adder fa3(
        .A(A[3]),
        .B(B[3]),
        .C_in(C[2]),
        .S(S[3]),
        .C_out(C_out)
    );

endmodule

module full_adder(
    input A,
    input B,
    input C_in,
    output S,
    output C_out
);

    assign S = A ^ B ^ C_in;
    assign C_out = (A & B) | (C_in & (A ^ B));

endmodule