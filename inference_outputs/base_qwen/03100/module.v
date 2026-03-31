
module top_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    input clk,
    output [31:0] result
);

    wire [15:0] sum1;
    wire [31:0] xor_b;
    wire cout1;
    wire [31:0] sum2;
    wire cout2;

    adder_module adder1(.a(a[15:0]), .b(b[15:0]), .cin(1'b0), .sum(sum1), .cout(cout1));
    adder_module adder2(.a(a[31:16]), .b(b[31:16]), .cin(cout1), .sum(sum2[31:16]), .cout(cout2));
    xor_gate xor1(.a(b), .b({sub, 31'b0}), .y(xor_b));
    adder_module adder3(.a(sum1), .b(xor_b[15:0]), .cin(sub), .sum(sum2[15:0]));

    assign result = sub ? sum2 : sum1;

endmodule
module adder_module(
    input [15:0] a,
    input [15:0] b,
    input cin,
    output [15:0] sum,
    output cout
);

    assign {cout, sum} = a + b + cin;

endmodule
module xor_gate(
    input [31:0] a,
    input [31:0] b,
    output [31:0] y
);

    assign y = a ^ b;

endmodule