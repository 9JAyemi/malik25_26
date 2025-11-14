module add_sub_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

    wire [31:0] inverted_b;
    wire [31:0] carry_out;
    wire [31:0] temp_sum;

    assign inverted_b = ~b;

    // Adder module
    adder_module adder(
        .a(a),
        .b(inverted_b),
        .carry_in(sub),
        .sum(temp_sum),
        .carry_out(carry_out)
    );

    // XOR gate
    assign sum = (sub) ? temp_sum + 1 : temp_sum;

endmodule

module adder_module(
    input [31:0] a,
    input [31:0] b,
    input carry_in,
    output [31:0] sum,
    output [31:0] carry_out
);

    assign {carry_out, sum} = a + b + carry_in;

endmodule