
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] sum;
    wire C1, C2, C3;

    full_adder adder1 (
        .a(A[0]),
        .b(B[0]),
        .cin(Cin),
        .sum(sum[0]),
        .cout(C1)
    );

    full_adder adder2 (
        .a(A[1]),
        .b(B[1]),
        .cin(C1),
        .sum(sum[1]),
        .cout(C2)
    );

    full_adder adder3 (
        .a(A[2]),
        .b(B[2]),
        .cin(C2),
        .sum(sum[2]),
        .cout(C3)
    );

    full_adder adder4 (
        .a(A[3]),
        .b(B[3]),
        .cin(C3),
        .sum(sum[3]),
        .cout(Cout)
    );

    assign S = sum;

endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);

endmodule
