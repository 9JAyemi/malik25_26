module d_flip_flop_chain (
    input clk,
    input [7:0] d,
    output [7:0] q
);

reg [7:0] q_reg;
wire [7:0] d_wire;

assign d_wire = {q_reg[6:0], d};

always @(negedge clk) begin
    q_reg <= d_wire;
end

assign q = q_reg;

endmodule

module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

d_flip_flop_chain flip_flop_chain (
    .clk(clk),
    .d(d),
    .q(q)
);

endmodule