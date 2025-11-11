
module LUT1 (
    input I0,
    output O
);

assign O = (I0 == 1'b1) ? 1'b1 : 1'b0;

endmodule

module shift_register
(
    input [8:0]in,
    output [8:0]out,
    input clk
);

reg [8:0]shift_reg;

assign out[8] = shift_reg[8];
assign out[7] = shift_reg[7];
assign out[6] = shift_reg[6];
assign out[5] = shift_reg[5];
assign out[4] = shift_reg[4];
assign out[3] = shift_reg[3];
assign out[2] = shift_reg[2];
assign out[1] = shift_reg[1];
assign out[0] = shift_reg[0];

always @(posedge clk) begin
    shift_reg <= {shift_reg[7:0], in[8]};
end
endmodule
