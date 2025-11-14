
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
module four_bit_adder(
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum,
    output carry_out
);

    wire [3:0] fa_sum;
    wire [3:0] fa_carry_out;

    full_adder fa0(
        .a(a[0]),
        .b(b[0]),
        .carry_in(1'b0),
        .sum(fa_sum[0]),
        .carry_out(fa_carry_out[0])
    );

    full_adder fa1(
        .a(a[1]),
        .b(b[1]),
        .carry_in(fa_carry_out[0]),
        .sum(fa_sum[1]),
        .carry_out(fa_carry_out[1])
    );

    full_adder fa2(
        .a(a[2]),
        .b(b[2]),
        .carry_in(fa_carry_out[1]),
        .sum(fa_sum[2]),
        .carry_out(fa_carry_out[2])
    );

    full_adder fa3(
        .a(a[3]),
        .b(b[3]),
        .carry_in(fa_carry_out[2]),
        .sum(fa_sum[3]),
        .carry_out(carry_out)
    );

    assign sum = fa_sum;

endmodule