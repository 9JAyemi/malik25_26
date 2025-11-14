module crc_ccitt (
    input [15:0] data_in,
    input wire clk,
    output wire [7:0] crc_out
);

reg [15:0] shift_reg;
reg [7:0] crc_reg;

always @(*) begin
    shift_reg[15:0] = {shift_reg[14:0], data_in[15:0]};
end

always @(posedge clk) begin
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[15] ? 8'h00 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[14] ? 8'h10 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[13] ? 8'h20 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[12] ? 8'h30 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[11] ? 8'h40 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[10] ? 8'h50 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[9] ? 8'h60 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[8] ? 8'h70 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[7] ? 8'h80 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[6] ? 8'h90 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[5] ? 8'ha0 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[4] ? 8'hb0 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[3] ? 8'hc0 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[2] ? 8'hd0 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[1] ? 8'he0 : 8'h00);
    crc_reg[7:0] = crc_reg[7:0] ^ (shift_reg[0] ? 8'hf0 : 8'h00);
    
    if (crc_reg[7]) begin
        crc_reg[6:0] = (crc_reg[6:0] << 1) ^ 8'h07;
    end else begin
        crc_reg[6:0] = crc_reg[6:0] << 1;
    end
end

assign crc_out = crc_reg[7:0];

endmodule