module dual_edge_ff (
    input clk,
    input d,
    output q
);

wire d_ff1_out, d_ff2_out, and_gate_out;

DFF d_ff1(.clk(clk), .d(d), .q(d_ff1_out));
DFF d_ff2(.clk(clk), .d(d_ff1_out), .q(d_ff2_out));
AND and_gate(.a(d_ff1_out), .b(~d_ff2_out), .out(and_gate_out));
DFF d_ff3(.clk(clk), .d(and_gate_out), .q(q));

endmodule

module DFF (
    input clk,
    input d,
    output q
);

reg q;

always @(posedge clk) begin
    q <= d;
end

endmodule

module AND (
    input a,
    input b,
    output out
);

assign out = a & b;

endmodule