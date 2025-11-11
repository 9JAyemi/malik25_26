
module video_sys_jtag_uart_0_sim_scfifo_r (
    // inputs:
    clk,
    fifo_rd,
    rst_n,

    // outputs:
    fifo_EF,
    fifo_rdata,
    rfifo_full,
    rfifo_used
);
    output fifo_EF;
    output [7:0] fifo_rdata;
    output rfifo_full;
    output [5:0] rfifo_used;

    input clk;
    input fifo_rd;
    input rst_n;

    reg [63:0] fifo;
    reg [5:0] rfifo_used;
    reg [7:0] fifo_rdata_r;

    assign fifo_EF = (rfifo_used == 0);
    assign rfifo_full = (rfifo_used == 64);

    always @(posedge clk) begin
        if (rst_n == 0) begin
            fifo <= 64'h0;
            rfifo_used <= 6'h0;
        end else if (fifo_rd) begin
            fifo_rdata_r <= fifo[7:0];
            rfifo_used <= rfifo_used - 1;
            fifo <= {fifo[55:0], 8'h00};
        end else begin
            if (rfifo_used < 64) begin
                fifo <= {fifo[55:0], 8'h00};
                rfifo_used <= rfifo_used + 1;
            end
        end
    end

    assign fifo_rdata = fifo_rdata_r;
endmodule
