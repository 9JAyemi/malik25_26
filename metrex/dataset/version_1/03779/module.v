
module top_module(
    input a,
    input b,
    input sel_xor,
    input sel_mux,
    output wire out_always
);

wire xor_out;
wire mux_out;

xor_gate xor_inst(
    .a(a),
    .b(b),
    .out(xor_out)
);

mux_2to1 mux_inst(
    .a(a),
    .b(b),
    .sel(sel_mux),
    .out(mux_out)
);

assign out_always = (sel_xor & ~sel_mux) ? xor_out :
                    (sel_mux & ~sel_xor) ? mux_out :
                    (sel_mux & sel_xor) ? 1'b1 : 1'b0;

endmodule
module xor_gate(
    input a,
    input b,
    output wire out
);

assign out = a ^ b;

endmodule
module mux_2to1(
    input a,
    input b,
    input sel,
    output wire out
);

assign out = sel ? b : a;

endmodule