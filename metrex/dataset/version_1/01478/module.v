module top_module(
    input [31:0] a,
    input [31:0] b,
    input select,
    output [31:0] sum
);

    wire [15:0] a_low, b_low;
    wire carry_in;
    wire [15:0] sum_low;

    // Split the input numbers into high and low halves
    assign a_low = a[15:0];
    assign b_low = b[15:0];

    // Instantiate the 16-bit adder module
    adder16bit adder(
        .a(a_low),
        .b(b_low),
        .carry_in(carry_in),
        .sum(sum_low)
    );

    // Perform addition or subtraction based on select input
    assign carry_in = (select) ? ~b[15] : 1'b0;
    assign sum = (select) ? {~b,1'b1} + a : {sum_low,a[31:16]} + {a_low,b_low};

endmodule

// 16-bit adder module
module adder16bit(
    input [15:0] a,
    input [15:0] b,
    input carry_in,
    output [15:0] sum
);

    wire [15:0] sum_temp;

    assign sum_temp = a + b + carry_in;
    assign sum = sum_temp;

endmodule