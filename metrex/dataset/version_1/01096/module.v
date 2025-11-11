
module memory_64bit_4bank(
    input clk,
    input [63:0] din,
    input wr_en,
    input [1:0] wr_addr,
    input rd_en,
    input [1:0] rd_addr,
    output [63:0] dout,
    output full
);
reg [15:0] mem [0:1023];
reg [63:0] dout_tmp;       // declare dout_tmp as a register
assign full = 0; 

always @(posedge clk) begin
    if (wr_en) begin
        case (wr_addr)
            2'b00: begin
                mem[wr_addr*4+3] <= din[15:0];
                mem[wr_addr*4+2] <= din[31:16];
                mem[wr_addr*4+1] <= din[47:32];
                mem[wr_addr*4+0] <= din[63:48];
            end
            2'b01: begin
                mem[wr_addr*4+3] <= din[15:0];
                mem[wr_addr*4+2] <= din[31:16];
                mem[wr_addr*4+1] <= din[47:32];
                mem[wr_addr*4+0] <= din[63:48];
            end
            2'b10: begin
                mem[wr_addr*4+3] <= din[15:0];
                mem[wr_addr*4+2] <= din[31:16];
                mem[wr_addr*4+1] <= din[47:32];
                mem[wr_addr*4+0] <= din[63:48];
            end
            2'b11: begin
                mem[wr_addr*4+3] <= din[15:0];
                mem[wr_addr*4+2] <= din[31:16];
                mem[wr_addr*4+1] <= din[47:32];
                mem[wr_addr*4+0] <= din[63:48];
            end
        endcase
    end
    if (rd_en) begin
        case (rd_addr)
            2'b00: dout_tmp <= {mem[rd_addr*4+3], mem[rd_addr*4+2], mem[rd_addr*4+1], mem[rd_addr*4+0]};
            2'b01: dout_tmp <= {mem[rd_addr*4+3], mem[rd_addr*4+2], mem[rd_addr*4+1], mem[rd_addr*4+0]};
            2'b10: dout_tmp <= {mem[rd_addr*4+3], mem[rd_addr*4+2], mem[rd_addr*4+1], mem[rd_addr*4+0]};
            2'b11: dout_tmp <= {mem[rd_addr*4+3], mem[rd_addr*4+2], mem[rd_addr*4+1], mem[rd_addr*4+0]};
        endcase
    end
end
assign dout = dout_tmp;
endmodule