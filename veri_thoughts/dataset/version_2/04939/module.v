module top_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

    wire [15:0] a_low = a[15:0];
    wire [15:0] a_high = a[31:16];
    wire [15:0] b_low = b[15:0];
    wire [15:0] b_high = b[31:16];
    wire [15:0] sum_low;
    wire [15:0] sum_high;
    wire carry;

    // Instantiate the two 16-bit adder modules
    adder16 adder_low(
        .a(a_low),
        .b(b_low),
        .cin(sub),
        .sum(sum_low),
        .cout(carry)
    );

    adder16 adder_high(
        .a(a_high),
        .b(b_high),
        .cin(carry),
        .sum(sum_high),
        .cout()
    );

    // Use a 32-bit multiplexer to select between the addition and subtraction outputs
    assign sum = sub ? {sum_high, sum_low} - 1 : {sum_high, sum_low};

endmodule

// 16-bit adder module
module adder16(
    input [15:0] a,
    input [15:0] b,
    input cin,
    output [15:0] sum,
    output cout
);

    assign {cout, sum} = a + b + cin;

endmodule