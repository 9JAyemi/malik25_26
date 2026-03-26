
module top_module(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

wire [31:0] inverted_b;

assign inverted_b = sub ? ~b : b;

cla_adder_32bit adder(
    .a(a),
    .b(inverted_b),
    .cin(sub),
    .sum(sum)
);

endmodule
module cla_adder_32bit(
    input [31:0] a,
    input [31:0] b,
    input cin,
    output [31:0] sum
);

wire [31:0] g;
wire [31:0] p;
wire [31:0] c;

assign g = a & b;
assign p = a ^ b;
assign c[0] = cin;

genvar i;
generate
    for (i = 0; i < 31; i = i + 1) begin : gen
        assign c[i+1] = g[i] | (p[i] & c[i]);
        assign sum[i] = p[i] ^ c[i];
    end
endgenerate

assign sum[31] = p[31] ^ c[31]; // Driver for the last bit of sum

endmodule