
module top_module(
    input [3:0] a,
    input [3:0] b,
    input sel_b1,
    input sel_b2,
    output [3:0] out_always,
    output [3:0] out_and,
    output [3:0] out_or,
    output [3:0] out_xor
);

    wire [3:0] mux1_out;
    wire [3:0] mux2_out;
    wire [3:0] adder_out;
    wire [3:0] and_out;
    wire [3:0] or_out;
    wire [3:0] xor_out;

    // 2-to-1 multiplexers
    mux2to1 mux1(.a(a), .b(b), .sel(sel_b1), .out(mux1_out));
    mux2to1 mux2(.a(a), .b(b), .sel(sel_b2), .out(mux2_out));

    // 4-bit adder
    adder add(.a(mux1_out), .b(mux2_out), .out(adder_out));

    // Bitwise AND, OR, and XOR
    assign and_out = a & b;
    assign or_out = a | b;
    assign xor_out = a ^ b;

    // Output selection
    assign out_and = sel_b1 && sel_b2 ? and_out : 4'b0;
    assign out_or = sel_b1 && sel_b2 ? or_out : 4'b0;
    assign out_xor = sel_b1 && sel_b2 ? xor_out : 4'b0;
    assign out_always = sel_b1 == 0 && sel_b2 == 0 ? adder_out : sel_b1 ? mux2_out : mux1_out;

endmodule

module mux2to1(
    input [3:0] a,
    input [3:0] b,
    input sel,
    output [3:0] out
);

    assign out = sel ? b : a;

endmodule

module adder(
    input [3:0] a,
    input [3:0] b,
    output [3:0] out
);

    assign out = a + b;

endmodule
