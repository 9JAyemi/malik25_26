
module top_module (
    input [31:0] a,
    input [31:0] b,
    input sub_select,
    output [31:0] sum
);

    wire [31:0] add_out;
    wire [31:0] sub_out;
    wire [31:0] and_out;
    wire carry_out;
    wire overflow;

    adder_subtractor add_sub(
        .a(a),
        .b(b),
        .sub_select(sub_select),
        .add_out(add_out),
        .sub_out(sub_out),
        .carry_out(carry_out),
        .overflow(overflow)
    );
    functional_logic func(
        .in1(add_out),
        .in2(sub_out),
        .out(and_out),
        .carry_in(carry_out),
        .overflow_in(overflow)
    );

    assign sum = sub_select ? sub_out : add_out;

endmodule
module adder_subtractor (
    input [31:0] a,
    input [31:0] b,
    input sub_select,
    output [31:0] add_out,
    output [31:0] sub_out,
    output carry_out,
    output overflow
);

    wire [31:0] a_inv;
    wire [31:0] b_inv;
    wire [31:0] sub_b_inv;
    wire sub_carry_in;
    wire add_carry_in;
    wire add_overflow;
    wire sub_overflow;

    assign a_inv = ~a;
    assign b_inv = ~b;
    assign sub_b_inv = b_inv + 32'b1;
    assign sub_carry_in = sub_select;
    assign add_carry_in = 1'b0;

    adder add(
        .a(a),
        .b(b),
        .carry_in(add_carry_in),
        .sum(add_out),
        .carry_out(add_overflow)
    );
    adder sub(
        .a(a),
        .b(sub_b_inv),
        .carry_in(sub_carry_in),
        .sum(sub_out),
        .carry_out(sub_overflow)
    );

    assign carry_out = sub_select ? sub_carry_in : add_carry_in;
    assign overflow = sub_select ? sub_overflow : add_overflow;

endmodule
module functional_logic (
    input [31:0] in1,
    input [31:0] in2,
    output [31:0] out,
    input carry_in,
    input overflow_in
);

    assign out = in1 & in2 & ~carry_in & ~overflow_in;

endmodule
module adder (
    input [31:0] a,
    input [31:0] b,
    input carry_in,
    output [31:0] sum,
    output carry_out
);

    assign {carry_out, sum} = a + b + carry_in;

endmodule