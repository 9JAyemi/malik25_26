module pipelined_adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);

wire [7:0] p, g, c;

assign p = a ^ b;
assign g = a & b;
assign c[0] = 1'b0;

genvar i;

generate
    for (i = 1; i < 8; i = i + 1) begin : carry_lookahead
        assign c[i] = g[i-1] | (p[i-1] & c[i-1]);
    end
endgenerate

assign s = a + b + c;

assign overflow = (a[7] == b[7]) && (a[7] != s[7]);

endmodule

module top_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);

pipelined_adder adder(a, b, s, overflow);

endmodule