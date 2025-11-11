
module four_bit_adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    wire [4:0] c;
    wire [3:0] g;
    wire [3:0] p;

    assign g = a ^ b;
    assign p = a & b;

    assign c[0] = cin;
    assign c[4:1] = {p[3], g[2], g[1], g[0]};

    assign sum = g + c[4:1];
    assign cout = c[4];

endmodule