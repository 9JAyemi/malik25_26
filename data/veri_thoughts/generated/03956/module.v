
module pipelined_xor(
    input clk,
    input a,
    input b,
    output wire out_comb
);

reg a_reg, b_reg;
reg out_reg;

always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
    out_reg <= a_reg ^ b_reg;
end

assign out_comb = out_reg;

endmodule
