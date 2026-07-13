module shift_reg_mux_xor (
    input clk,
    input d,
    input [255:0] in,
    input [7:0] sel,
    output q
);

reg [2:0] shift_reg;
wire [7:0] mux_sel;
wire [0:255] mux_out;

// Shift register
always @(posedge clk) begin
    shift_reg <= {shift_reg[1:0], d};
end

// Multiplexer
assign mux_sel = sel;
assign mux_out = {in[255:248], in[247:240], in[239:232], in[231:224], in[223:216], in[215:208], in[207:200], in[199:192], in[191:184], in[183:176], in[175:168], in[167:160], in[159:152], in[151:144], in[143:136], in[135:128], in[127:120], in[119:112], in[111:104], in[103:96], in[95:88], in[87:80], in[79:72], in[71:64], in[63:56], in[55:48], in[47:40], in[39:32], in[31:24], in[23:16], in[15:8], in[7:0]};
assign q = shift_reg[0] ^ mux_out[mux_sel];

endmodule