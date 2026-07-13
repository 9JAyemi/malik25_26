module adder_16bit(
    input [15:0] a,
    input [15:0] b,
    input cin,
    output [15:0] sum,
    output cout
);

    assign {cout, sum} = a + b + cin;

endmodule

module carry_select_adder(
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);
    wire [15:0] sum_lower, sum_upper_cin0, sum_upper_cin1;
    wire cout_lower, cout_upper_cin0, cout_upper_cin1, cout_final;

    adder_16bit lower_half_adder(
        .a(a[15:0]),
        .b(b[15:0]),
        .cin(1'b0),
        .sum(sum_lower),
        .cout(cout_lower)
    );

    // Upper half assuming carry in is 0
    adder_16bit upper_half_adder_cin0(
        .a(a[31:16]),
        .b(b[31:16]),
        .cin(1'b0),
        .sum(sum_upper_cin0),
        .cout(cout_upper_cin0)
    );

    adder_16bit upper_half_adder_cin1(
        .a(a[31:16]),
        .b(b[31:16]),
        .cin(1'b1),
        .sum(sum_upper_cin1),
        .cout(cout_upper_cin1)
    );

    assign sum[31:16] = cout_lower ? sum_upper_cin1 : sum_upper_cin0;
    assign sum[15:0] = sum_lower;
endmodule

module top_module(
    input [31:0] a,
    input [31:0] b,
    output [31:0] sum
);

    carry_select_adder adder(
        .a(a),
        .b(b),
        .sum(sum)
    );

endmodule
