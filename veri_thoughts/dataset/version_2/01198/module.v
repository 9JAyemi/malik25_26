
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output [4:0] S
);

    wire [3:0] sum;
    wire carry_out;

    assign {carry_out, sum} = A + B;
    assign S = {carry_out, sum};

endmodule