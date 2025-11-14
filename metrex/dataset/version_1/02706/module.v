module fifo
(
    input clk,
    input rst,
    input [15:0] din,
    input wr_en,
    input rd_en,
    output reg [15:0] dout,
    output reg empty,
    output reg full
);

reg [15:0] mem [0:7];
reg [2:0] wr_ptr = 0;
reg [2:0] rd_ptr = 0;

always @(posedge clk) begin
    if (rst) begin
        wr_ptr <= 0;
        rd_ptr <= 0;
        empty <= 1;
        full <= 0;
    end else begin
        if (wr_en && !full) begin
            mem[wr_ptr] <= din;
            wr_ptr <= wr_ptr + 1;
            if (wr_ptr == 7) begin
                wr_ptr <= 0;
            end
            empty <= 0;
            if (wr_ptr == rd_ptr) begin
                full <= 1;
            end
        end
        if (rd_en && !empty) begin
            dout <= mem[rd_ptr];
            rd_ptr <= rd_ptr + 1;
            if (rd_ptr == 7) begin
                rd_ptr <= 0;
            end
            full <= 0;
            if (rd_ptr == wr_ptr) begin
                empty <= 1;
            end
        end
    end
end

endmodule
