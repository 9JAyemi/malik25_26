module full_adder(
    input a,
    input b,
    input carry_in,
    output sum,
    output carry_out
);

    assign sum = a ^ b ^ carry_in;
    assign carry_out = (a & b) | (a & carry_in) | (b & carry_in);

endmodule

module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    output [4:0] C
);

    wire [3:0] sum;
    wire [4:0] carry;

    full_adder fa0(
        .a(A[0]),
        .b(B[0]),
        .carry_in(1'b0),
        .sum(sum[0]),
        .carry_out(carry[1])
    );

    full_adder fa1(
        .a(A[1]),
        .b(B[1]),
        .carry_in(carry[1]),
        .sum(sum[1]),
        .carry_out(carry[2])
    );

    full_adder fa2(
        .a(A[2]),
        .b(B[2]),
        .carry_in(carry[2]),
        .sum(sum[2]),
        .carry_out(carry[3])
    );

    full_adder fa3(
        .a(A[3]),
        .b(B[3]),
        .carry_in(carry[3]),
        .sum(sum[3]),
        .carry_out(carry[4])
    );

    assign C = {carry[4], sum};

endmodule