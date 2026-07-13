
module mux_2to1 (
    input a,
    input b,
    input sel,
    output reg out
);

always @ (sel or a or b) begin
    out = sel ? b : a;
end

endmodule
module top_module(
    input a,
    input b,
    input sel_b1,
    input sel_b2,
    output reg out_always
);

wire sel = (sel_b1 & sel_b2);

mux_2to1 mux (
    .a(a),
    .b(b),
    .sel(sel),
    .out(out_always)
);

endmodule