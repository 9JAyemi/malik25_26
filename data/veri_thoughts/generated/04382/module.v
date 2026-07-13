module adder_16bit (
    input [15:0] operand1,
    input [15:0] operand2,
    input carry_in,
    output [15:0] sum,
    output carry_out
);

    assign {carry_out, sum} = operand1 + operand2 + carry_in;

endmodule