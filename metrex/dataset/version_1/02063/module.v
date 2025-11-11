
module afifo_sram #(
    parameter DEPTH =256,
    parameter ADDRESS_WIDTH = 8, 
    parameter WIDTH=8
)(
    input CLK,
    input REN,
    input WEN,
    input RESET,
    input valid_in,
    input [WIDTH-1:0] Data_in,
    output [WIDTH-1:0] Data_out,
    output Full_out,
    output Empty_out
);


reg [ADDRESS_WIDTH-1:0] read_ptr;
reg [ADDRESS_WIDTH-1:0] write_ptr;
wire [ADDRESS_WIDTH-1:0] next_write_ptr;
wire [ADDRESS_WIDTH-1:0] next_read_ptr;
wire [ADDRESS_WIDTH-1:0] mem_addr;
reg [WIDTH-1:0] mem [DEPTH-1:0];

assign mem_addr = REN ? read_ptr : write_ptr;
assign Data_out = mem[mem_addr];

assign Full_out = (next_write_ptr == read_ptr) & (REN==1'b0);
assign Empty_out = (write_ptr == read_ptr) & (WEN==1'b0);

always @(posedge CLK) begin
    if (RESET) begin
        read_ptr <= 0;
        write_ptr <= 0;
    end else begin
        if (WEN && !Full_out) begin
            mem[write_ptr] <= Data_in;
            write_ptr <= next_write_ptr;
        end
        if (REN && !Empty_out && valid_in) begin
            read_ptr <= next_read_ptr;
        end
    end
end

assign next_write_ptr = (write_ptr == DEPTH-1) ? 0 : write_ptr + 1;
assign next_read_ptr = (read_ptr == DEPTH-1) ? 0 : read_ptr + 1;

endmodule