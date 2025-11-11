module dual_edge_triggered_ff (
    input clk,
    input d,
    output q
);

reg d1, d2, q1, q2;

always @(posedge clk) begin
    d1 <= d;
    q1 <= d1;
end

always @(negedge clk) begin
    d2 <= q1;
    q2 <= d2;
end

assign q = q2;

endmodule

module top_module (
    input clk,
    input d,
    output q
);

wire q_ff;

dual_edge_triggered_ff ff1 (
    .clk(clk),
    .d(d),
    .q(q_ff)
);

dual_edge_triggered_ff ff2 (
    .clk(clk),
    .d(q_ff),
    .q(q)
);

endmodule