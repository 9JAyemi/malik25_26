module crc #(
    parameter CRC_WIDTH     = 32,
    parameter DATA_WIDTH    = 8,
    parameter POLYNOMIAL    = 32'h04C11DB7,
    parameter SEED          = 32'hFFFFFFFF
)(
    input clk,
    input rst,
    input [DATA_WIDTH-1:0] data_in,
    output reg [CRC_WIDTH-1:0] crc_out
);

reg [CRC_WIDTH-1:0] crc_reg;
reg [CRC_WIDTH-1:0] polynomial;

always @(posedge clk) begin
    if (rst) begin
        crc_reg <= SEED;
    end else begin
        crc_reg <= crc_reg << DATA_WIDTH;
        crc_reg[DATA_WIDTH-1:0] <= crc_reg[DATA_WIDTH-1:0] ^ data_in;

        if (crc_reg[CRC_WIDTH-1]) begin
            crc_reg <= crc_reg ^ polynomial;
        end
    end
end

always @* begin
    polynomial = POLYNOMIAL;
end

always @* begin
    crc_out = ~crc_reg;
end

endmodule