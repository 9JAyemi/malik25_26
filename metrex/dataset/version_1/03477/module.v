
module pipelined_adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);

    wire [7:0] p, g, c;

    assign p[0] = a[0] ^ b[0];
    assign g[0] = a[0] & b[0];
    assign c[0] = g[0];

    genvar i;
    generate
        for (i = 1; i < 8; i = i + 1) begin
            assign p[i] = a[i] ^ b[i] ^ c[i-1];
            assign g[i] = (a[i] & b[i]) | (a[i] & c[i-1]) | (b[i] & c[i-1]);
            assign c[i] = (a[i] & b[i]) | (g[i] & c[i-1]);
        end
    endgenerate

    assign s = p ^ c;
    assign overflow = (a[7] == b[7]) && (a[7] != s[7]);

endmodule
module top_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] s,
    output overflow
);

    wire [7:0] p, g, c;
    wire [7:0] p1, g1, c1;

    pipelined_adder adder1(.a(a), .b(b), .s(p1), .overflow(overflow));
    pipelined_adder adder2(.a(p1), .b(8'b0), .s(s), .overflow()); // 'overflow' is unconnected, this should not cause an error

endmodule