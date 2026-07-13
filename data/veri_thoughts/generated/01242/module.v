
module adder (
    input [7:0] a,
    input [7:0] b,
    output [8:0] c
);

    wire [8:0] sum;
    wire carry;

    assign {carry, sum[7:0]} = a + b;

    assign c = {carry, sum[7:0]};

endmodule