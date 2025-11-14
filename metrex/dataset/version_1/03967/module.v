module shift_register (
    input clk,
    input [7:0] d,
    output [7:0] q
);

reg [7:0] shift_reg;

always @(posedge clk) begin
    shift_reg <= {shift_reg[6:0], d};
end

assign q = shift_reg;

endmodule

module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

shift_register sr (
    .clk(clk),
    .d(d),
    .q(q)
);

endmodule