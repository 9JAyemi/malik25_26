
module ripple_carry_adder(
    input [3:0] a, b, c,
    output [3:0] sum,
    output carry_out
);

    wire [3:0] s1, s2, s3;
    wire c1, c2;

    // Full Adder 1
    full_adder fa1(
        .a(a[0]),
        .b(b[0]),
        .c(c[0]),
        .sum(s1[0]),
        .carry_out(c1)
    );

    // Full Adder 2
    full_adder fa2(
        .a(a[1]),
        .b(b[1]),
        .c(c1),
        .sum(s1[1]),
        .carry_out(c2)
    );

    // Full Adder 3
    full_adder fa3(
        .a(a[2]),
        .b(b[2]),
        .c(c2),
        .sum(s1[2]),
        .carry_out(carry_out)
    );

    // Full Adder 4
    full_adder fa4(
        .a(a[3]),
        .b(b[3]),
        .c(carry_out),
        .sum(s1[3]),
        .carry_out()
    );

    // Add 0x05
    add_5 adder(
        .in(s1),
        .out(s2)
    );

    // Output sum
    assign sum = s2;

endmodule
module full_adder(
    input a, b, c,
    output sum, carry_out
);

    assign {carry_out, sum} = a + b + c;

endmodule
module add_5(
    input [3:0] in,
    output [3:0] out
);

    assign out = in + 4'b0101;

endmodule
module top_module(
    input [3:0] a, b, c,
    output [3:0] result
);

    wire [3:0] sum;
    wire carry_out;

    ripple_carry_adder rca(
        .a(a),
        .b(b),
        .c(c),
        .sum(sum),
        .carry_out(carry_out)
    );

    add_5 adder(
        .in(sum),
        .out(result)
    );

endmodule