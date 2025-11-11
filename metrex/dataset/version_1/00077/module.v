module xor_flipflop (
    input clk,
    input a,
    input b,
    output reg q
);

reg xor_out;

always @ (a or b) begin
    xor_out = a ^ b;
end

always @(posedge clk) begin
    q <= xor_out;
end

endmodule


module dual_edge_ff (
    input clk,
    input d,
    output reg q
);

reg q1, q2;

always @(posedge clk) begin
    q1 <= d;
end

always @(negedge clk) begin
    q2 <= q1;
end

always @(posedge clk) begin
    q <= q2;
end

endmodule


module combined_module (
    input clk,
    input a,
    input b,
    output q
);

wire xor_out;
wire dual_edge_out;

xor_flipflop xor_inst (
    .clk(clk),
    .a(a),
    .b(b),
    .q(xor_out)
);

dual_edge_ff dual_edge_inst (
    .clk(clk),
    .d(xor_out),
    .q(dual_edge_out)
);

assign q = dual_edge_out;

endmodule


module top_module (
    input clk,
    input a,
    input b,
    output q
);

combined_module combined_inst (
    .clk(clk),
    .a(a),
    .b(b),
    .q(q)
);

endmodule