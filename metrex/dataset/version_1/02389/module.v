
module fifo_buffer (
    input clk,
    input reset,
    output reg if_empty_n,
    input if_read_ce,
    input if_read,
    output reg [7:0] if_dout,
    output reg if_full_n,
    input if_write_ce,
    input if_write,
    input [7:0] if_din
);

parameter ADDR_WIDTH = 1;
parameter DEPTH = 2;

reg [ADDR_WIDTH:0] wr_ptr = 0;
reg [ADDR_WIDTH:0] rd_ptr = 0;
reg [7:0] mem [0:DEPTH-1];
reg [ADDR_WIDTH:0] count = 0;

always @(posedge clk) begin
    if (reset == 1) begin
        wr_ptr <= 0;
        rd_ptr <= 0;
        count <= 0;
    end else begin
        if (if_write & if_write_ce & if_full_n) begin
            mem[wr_ptr] <= if_din;
            wr_ptr <= wr_ptr + 1;
            count <= count + 1;
            if (wr_ptr == DEPTH) begin
                wr_ptr <= 0;
            end
        end
        if (if_read & if_read_ce & if_empty_n) begin
            if_dout <= mem[rd_ptr];
            rd_ptr <= rd_ptr + 1;
            count <= count - 1;
            if (rd_ptr == DEPTH) begin
                rd_ptr <= 0;
            end
        end
    end
    if_empty_n <= (count > 0);
    if_full_n <= (count < DEPTH);
end

endmodule
