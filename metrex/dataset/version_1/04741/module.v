module fifo_buffer (
    input clk,
    input fifo_clear,
    input fifo_rd,
    input rst_n,
    input [7:0] t_dat,
    input wr_rfifo,
    output fifo_EF,
    output reg [7:0] fifo_rdata,
    output rfifo_full,
    output [5:0] rfifo_used
);

    reg [7:0] fifo [63:0];
    reg [5:0] fifo_ptr;
    wire fifo_full;
    wire fifo_empty;

    assign fifo_full = (fifo_ptr == 63);
    assign fifo_empty = (fifo_ptr == 0);

    always @(posedge clk) begin
        if (!rst_n) begin
            fifo_ptr <= 0;
        end else if (fifo_clear) begin
            fifo_ptr <= 0;
        end else if (wr_rfifo && !fifo_full) begin
            fifo[fifo_ptr] <= t_dat;
            fifo_ptr <= fifo_ptr + 1;
        end else if (fifo_rd && !fifo_empty) begin
            fifo_rdata <= fifo[0];
            fifo_ptr <= fifo_ptr - 1;
        end
    end

    assign fifo_EF = fifo_empty;
    assign rfifo_full = fifo_full;
    assign rfifo_used = fifo_ptr;

endmodule