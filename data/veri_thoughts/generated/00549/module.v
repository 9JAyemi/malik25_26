
module top_module(
    input a,
    input b,
    input sel_b1,
    input sel_b2,
    output reg out_always
);

wire and_out;
wire mux_out;
wire final_out;

and_gate and_inst(
    .a(a),
    .b(b),
    .out(and_out)
);

mux_2to1 mux_inst(
    .a(a),
    .b(b),
    .sel(sel_b1 & sel_b2),
    .out(mux_out)
);

functional_module functional_inst(
    .and_out(and_out),
    .mux_out(mux_out),
    .final_out(final_out)
);

always @* begin
    out_always = final_out;
end

endmodule
module and_gate(
    input a,
    input b,
    output reg out
);

always @* begin
    out = a & b;
end

endmodule
module mux_2to1(
    input a,
    input b,
    input sel,
    output reg out
);

always @* begin
    out = sel ? b : a;
end

endmodule
module functional_module(
    input and_out,
    input mux_out,
    output reg final_out
);

always @* begin
    final_out = and_out ^ mux_out;
end

endmodule