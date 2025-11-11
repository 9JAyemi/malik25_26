module sync_fifo #(
    parameter DWIDTH = 16,
    parameter DEPTH = 8
) (
    input clk,
    input res_n,
    input [DWIDTH-1:0] d_in,
    input shift_in,
    input shift_out,
    output reg [DWIDTH-1:0] d_out,
    output reg full,
    output reg empty,
    output wire almost_full,
    output wire almost_empty
);

    reg [DWIDTH-1:0] buffer [DEPTH-1:0];
    reg [DEPTH-1:0] fill_level;
    reg [DEPTH-1:0] read_pointer;
    reg [DEPTH-1:0] write_pointer;
    
    always @(posedge clk, negedge res_n) begin
        if (~res_n) begin
            d_out <= 0;
            fill_level <= 0;
            read_pointer <= 0;
            write_pointer <= 0;
            empty <= 1;
            full <= 0;
        end else begin
            if (shift_out && ~empty) begin
                d_out <= buffer[read_pointer];
                read_pointer <= read_pointer + 1;
                if (read_pointer == write_pointer) begin
                    empty <= 1;
                end
                fill_level <= fill_level - 1;
                full <= 0;
            end else if (shift_in && ~full) begin
                buffer[write_pointer] <= d_in;
                write_pointer <= write_pointer + 1;
                if (write_pointer == read_pointer) begin
                    full <= 1;
                end
                fill_level <= fill_level + 1;
                empty <= 0;
            end else begin
                d_out <= d_out;
            end
        end
    end
    
    assign almost_full = (fill_level >= DEPTH-1);
    assign almost_empty = (fill_level <= 1);
    
endmodule