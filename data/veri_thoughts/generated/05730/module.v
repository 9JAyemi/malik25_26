module comb_logic(
    input a,
    input b,
    input select,
    input clk,
    output reg out_always_ff
);

wire xor_out;
wire or_out;
wire not_select;

assign not_select = ~select;
assign xor_out = (a & ~b) | (~a & b);
assign or_out = a | b;

always @(posedge clk) begin
    if (not_select) begin
        out_always_ff <= xor_out;
    end else begin
        out_always_ff <= or_out;
    end
end

endmodule
