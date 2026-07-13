
module four_bit_adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    wire [3:0] c;
    assign c[0] = cin;
    assign c[1] = 0;
    assign c[2] = 0;
    assign c[3] = 0;
    assign {cout, sum} = a + b + c;

endmodule