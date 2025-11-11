module add_sub_pipeline(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

    wire [15:0] a_lo, b_lo, sum_lo;
    wire [15:0] a_hi, b_hi, sum_hi;
    wire carry;

    // Instantiate the 16-bit adder module twice
    adder16bit adder_lo(.a(a_lo), .b(b_lo), .carry_in(sub), .sum(sum_lo), .carry_out(carry));
    adder16bit adder_hi(.a(a_hi), .b(b_hi), .carry_in(carry), .sum(sum_hi), .carry_out());

    // Connect the inputs to the 16-bit adders
    assign a_lo = a[15:0];
    assign b_lo = b[15:0] ^ (sub ? 32'hFFFF : 0);
    assign a_hi = a[31:16];
    assign b_hi = b[31:16] ^ (sub ? 32'hFFFF : 0);

    // Connect the outputs of the 16-bit adders to the output of the module
    assign sum = {sum_hi, sum_lo};

endmodule

module adder16bit(
    input [15:0] a,
    input [15:0] b,
    input carry_in,
    output [15:0] sum,
    output carry_out
);

    assign {carry_out, sum} = a + b + carry_in;

endmodule