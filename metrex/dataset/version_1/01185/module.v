
module dual_edge_triggered_ff (
    input clk,
    input d,
    output q
);

reg q;

always @(posedge clk) begin
    q <= d;
end

endmodule
module top_module (
    input clk,
    input d,
    output q
);

dual_edge_triggered_ff ff (
    .clk(clk),
    .d(d),
    .q(q)
);

endmodule