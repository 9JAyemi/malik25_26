
module reverse_bit_order(
    input [99:0] in,
    input clk,
    output [99:0] out
);

reg [99:0] shift_reg;
wire [99:0] reversed;

assign reversed[0] = shift_reg[99];

genvar i;
generate
    for (i = 1; i < 100; i = i + 1) begin : SHIFT_LOOP
        assign reversed[i] = shift_reg[99-i];
    end
endgenerate

assign out = reversed;

always @(posedge clk) begin
    shift_reg <= {shift_reg[98:0], in[0]};
end

endmodule
