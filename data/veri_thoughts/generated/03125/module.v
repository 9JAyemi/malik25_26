module full_adder (
    input A,
    input B,
    input C_in,
    output S,
    output C_out
);

    assign S = A ^ B ^ C_in;
    assign C_out = (A & B) | (C_in & (A ^ B));

endmodule

module adder_4bit (
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C_out
);

    wire [3:0] sum;
    wire carry_1, carry_2, carry_3;

    full_adder fa_1 (
        .A(A[0]),
        .B(B[0]),
        .C_in(1'b0),
        .S(sum[0]),
        .C_out(carry_1)
    );

    full_adder fa_2 (
        .A(A[1]),
        .B(B[1]),
        .C_in(carry_1),
        .S(sum[1]),
        .C_out(carry_2)
    );

    full_adder fa_3 (
        .A(A[2]),
        .B(B[2]),
        .C_in(carry_2),
        .S(sum[2]),
        .C_out(carry_3)
    );

    full_adder fa_4 (
        .A(A[3]),
        .B(B[3]),
        .C_in(carry_3),
        .S(sum[3]),
        .C_out(C_out)
    );

    assign S = sum;

endmodule