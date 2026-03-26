
module binary_adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum,
    output carry
);

    assign {carry, sum} = a + b;

endmodule

module bitwise_and (
    input [7:0] a,
    input [7:0] b,
    output [7:0] result
);

    assign result = a & b;

endmodule

module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [7:0] a, // 8-bit input for the binary adder
    input [7:0] b, // 8-bit input for the binary adder
    output [8:0] sum_and_carry // 9-bit output with MSB representing the carry bit
);

    wire [7:0] and_result;
    wire [7:0] adder_sum;
    wire adder_carry;

    binary_adder adder_inst (
        .a(a),
        .b(b),
        .sum(adder_sum),
        .carry(adder_carry)
    );

    bitwise_and and_inst (
        .a(a),
        .b(b),
        .result(and_result)
    );

    assign sum_and_carry = {adder_carry, and_result & adder_sum};

endmodule
