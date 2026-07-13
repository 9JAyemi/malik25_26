
module d_flip_flop (
    input clk,
    input d,
    output reg q
);
    always @(posedge clk) begin
        q <= d;
    end
endmodule

module comb_ops (
    input [99:0] in,
    output out_and,
    output out_or,
    output out_xor
);
    assign out_and = &in;
    assign out_or = |in;
    assign out_xor = ^in;
endmodule

module add_op (
    input a,
    input [2:0] b,
    output [7:0] out_add
);
    assign out_add = a + b;
endmodule

module top_module (
    input clk,
    input [99:0] in,
    output q,
    output out_and,
    output out_or,
    output out_xor,
    output [7:0] out_add
);
    wire d_ff_out;
    wire comb_and_out;
    wire comb_or_out;
    wire comb_xor_out;
    
    d_flip_flop d_ff (
        .clk(clk),
        .d(in[0]),
        .q(d_ff_out)
    );
    
    comb_ops comb (
        .in(in),
        .out_and(comb_and_out),
        .out_or(comb_or_out),
        .out_xor(comb_xor_out)
    );
    
    add_op add (
        .a(d_ff_out),
        .b({comb_and_out, comb_or_out, comb_xor_out}),
        .out_add(out_add)
    );
    
    assign q = d_ff_out;
    assign out_and = comb_and_out;
    assign out_or = comb_or_out;
    assign out_xor = comb_xor_out;
endmodule
