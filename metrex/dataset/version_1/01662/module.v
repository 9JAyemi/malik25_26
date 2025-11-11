
module small_fifo(
    input [31:0] data,
    input inclock,
    input outclock,
    input outclocken,
    output reg [31:0] q,
    input [4:0] rdaddress,
    input [4:0] wraddress,
    input wren
);

    parameter DEPTH = 16;
    parameter WIDTH = 32;

    reg [WIDTH-1:0] mem [DEPTH-1:0];
    reg [4:0] read_ptr, write_ptr;
    reg empty, full;

    wire new_empty = (read_ptr == write_ptr);
    wire new_full = (write_ptr == read_ptr - 1);

    always @(posedge inclock) begin
        if (wren && !full) begin
            mem[write_ptr] <= data;
            write_ptr <= (write_ptr == DEPTH-1) ? 0 : write_ptr + 1;
        end
        empty <= new_empty;
        full <= new_full;
    end

    always @(posedge outclock) begin
        if (outclocken && !empty) begin
            q <= mem[read_ptr];
            read_ptr <= (read_ptr == DEPTH-1) ? 0 : read_ptr + 1;
        end            
    end

endmodule