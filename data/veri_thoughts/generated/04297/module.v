
module encoder (
    input [7:0] in,
    input clk,
    output [2:0] out
);

reg [7:0] in_reg;
reg [2:0] out_reg;

always @(posedge clk) begin
    in_reg <= in;
end

always @(posedge clk) begin
    out_reg[0] <= in_reg[0] | in_reg[1] | in_reg[3] | in_reg[4] | in_reg[6];
    out_reg[1] <= in_reg[2] | in_reg[3] | in_reg[5] | in_reg[6] | in_reg[7];
    out_reg[2] <= in_reg[4] | in_reg[5] | in_reg[6] | in_reg[7];
end

assign out = out_reg;

endmodule
