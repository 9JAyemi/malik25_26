
module adder(
    input wire [7:0] a,
    input wire [7:0] b,
    input wire [15:0] sum_in,
    output wire [7:0] sum,
    output wire carry
);

    assign {carry, sum} = sum_in + {a, b};

endmodule
