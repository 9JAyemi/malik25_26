module adder (
    input wire [3:0] A,
    input wire [3:0] B,
    output wire [3:0] sum,
    output wire carry_out
);

assign {carry_out, sum} = A + B;

endmodule

module top_module (
    input wire [3:0] A,
    input wire [3:0] B,
    output wire [3:0] sum,
    output wire carry_out
);

adder add(A, B, sum, carry_out);

endmodule