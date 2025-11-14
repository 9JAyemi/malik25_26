
module ripple_adder(
    input [15:0] a,
    input [15:0] b,
    input cin,
    output [15:0] sum,
    output cout
);

    assign {cout, sum} = a + b + cin;

endmodule
module add_sub(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

    wire [15:0] a_lo = a[15:0];
    wire [15:0] a_hi = a[31:16];
    wire [15:0] b_lo = b[15:0];
    wire [15:0] b_hi = b[31:16];
    wire [15:0] sum_lo;
    wire [15:0] sum_hi;
    wire cout;

    // First 16-bit adder
    ripple_adder adder_lo(
        .a(a_lo),
        .b(sub ? ~b_lo : b_lo),
        .cin(sub),
        .sum(sum_lo),
        .cout(cout)
    );

    // Second 16-bit adder
    ripple_adder adder_hi(
        .a(a_hi),
        .b(sub ? ~b_hi : b_hi),
        .cin(cout),
        .sum(sum_hi),
        .cout()
    );

    // 32-bit XOR gate
    assign sum = {sum_hi, sum_lo} ^ (sub ? -1 : 0);

endmodule