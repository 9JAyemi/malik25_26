module fifo #(
    parameter MEM_STYLE = "auto",
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 1,
    parameter DEPTH = 2
) (
    input clk,
    input reset,
    input if_write_ce,
    input [DATA_WIDTH-1:0] if_write,
    input if_read_ce,
    output reg if_empty_n,
    output reg [DATA_WIDTH-1:0] if_dout,
    output reg if_full_n
);

reg [ADDR_WIDTH:0] write_ptr = 0;
reg [ADDR_WIDTH:0] read_ptr = 0;
reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];

always @(posedge clk) begin
    if (reset) begin
        write_ptr <= 0;
        read_ptr <= 0;
        if_empty_n <= 0;
        if_full_n <= 1;
    end else begin
        if (if_write_ce) begin
            mem[write_ptr] <= if_write;
            write_ptr <= write_ptr + 1;
            if (write_ptr == DEPTH) begin
                write_ptr <= 0;
            end
            if_empty_n <= 1;
            if (write_ptr == read_ptr) begin
                if_full_n <= 0;
            end
        end
        if (if_read_ce) begin
            if_dout <= mem[read_ptr];
            read_ptr <= read_ptr + 1;
            if (read_ptr == DEPTH) begin
                read_ptr <= 0;
            end
            if_full_n <= 1;
            if (read_ptr == write_ptr) begin
                if_empty_n <= 0;
            end
        end
    end
end

endmodule