module mux_pipeline(
    input a,
    input b,
    input sel_b1,
    input sel_b2,
    input clk,
    output reg out_always
);

reg mux_out1;
reg mux_out2;

always @(posedge clk) begin
    mux_out1 <= (sel_b1 & sel_b2) ? b : a;
    mux_out2 <= mux_out1;
    out_always <= mux_out2;
end

endmodule

module top_module(
    input a,
    input b,
    input sel_b1,
    input sel_b2,
    input clk,
    output out_always
);

mux_pipeline mux_inst(
    .a(a),
    .b(b),
    .sel_b1(sel_b1),
    .sel_b2(sel_b2),
    .clk(clk),
    .out_always(out_always)
);

endmodule