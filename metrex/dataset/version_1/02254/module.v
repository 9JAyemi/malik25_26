
module pipelined_add_sub(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] sum
);

wire [31:0] csa_out;
wire [31:0] cla_out;

// Carry save adder
csa csa_inst(
    .a(a),
    .b(b),
    .c(sub),
    .s(csa_out)
);

// Carry lookahead adder
cla cla_inst(
    .a(csa_out),
    .b({32{sub}}),
    .c(32'b0),
    .s(cla_out)
);

// Output sum
assign sum = cla_out;

endmodule
module csa(
    input [31:0] a,
    input [31:0] b,
    input c,
    output [31:0] s
);

wire [31:0] p;
wire [31:0] g;

// Generate and propagate signals
gen_propagate gen_propagate_inst(
    .a(a),
    .b(b),
    .p(p),
    .g(g)
);

// Sum calculation
assign s = p ^ c ^ g;

endmodule
module gen_propagate(
    input [31:0] a,
    input [31:0] b,
    output [31:0] p,
    output [31:0] g
);

assign p = a ^ b;
assign g = a & b;

endmodule
module cla(
    input [31:0] a,
    input [31:0] b,
    input [31:0] c,
    output [31:0] s
);

wire [31:0] p;
wire [31:0] g;

// Generate and propagate signals
gen_propagate gen_propagate_inst(
    .a(a),
    .b(b),
    .p(p),
    .g(g)
);

// Carry lookahead signals
wire [31:0] c0;
wire [31:0] c1;
wire [31:0] c2;
wire [31:0] c3;

assign c0 = c[0];
assign c1 = g[0] | (p[0] & c0);
assign c2 = g[1] | (p[1] & c1);
assign c3 = g[2] | (p[2] & c2);

// Sum calculation
assign s = p ^ c ^ (c3 << 3);

endmodule