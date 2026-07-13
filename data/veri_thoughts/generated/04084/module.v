
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output overflow
);

    wire [4:0] sum;
    wire carry;

    assign sum = A + B;
    assign carry = sum[4];

    assign S = sum[3:0];
    assign overflow = carry;

endmodule