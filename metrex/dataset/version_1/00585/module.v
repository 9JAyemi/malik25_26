module binary_adder(
    input [3:0] A,
    input [3:0] B,
    input carry_in,
    output [3:0] S,
    output carry_out
);

    wire [3:0] sum;
    wire [3:0] carry;

    // Full adder for each bit position
    full_adder fa0(
        .a(A[0]),
        .b(B[0]),
        .carry_in(carry_in),
        .sum(sum[0]),
        .carry_out(carry[0])
    );
    full_adder fa1(
        .a(A[1]),
        .b(B[1]),
        .carry_in(carry[0]),
        .sum(sum[1]),
        .carry_out(carry[1])
    );
    full_adder fa2(
        .a(A[2]),
        .b(B[2]),
        .carry_in(carry[1]),
        .sum(sum[2]),
        .carry_out(carry[2])
    );
    full_adder fa3(
        .a(A[3]),
        .b(B[3]),
        .carry_in(carry[2]),
        .sum(sum[3]),
        .carry_out(carry_out)
    );

    assign S = sum;

endmodule

module full_adder(
    input a,
    input b,
    input carry_in,
    output sum,
    output carry_out
);

    assign {carry_out, sum} = a + b + carry_in;

endmodule