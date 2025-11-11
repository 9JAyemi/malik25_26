module dual_edge_ff (
    input clk,
    input d,
    output q
);

reg q1, q2;

always @(posedge clk) begin
    q1 <= d;
end

always @(negedge clk) begin
    q2 <= q1;
end

assign q = q2;

endmodule

module top_module (
    input clk,
    input d,
    output q
);

dual_edge_ff ff (
    .clk(clk),
    .d(d),
    .q(q)
);

endmodule