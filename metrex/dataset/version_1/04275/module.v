module chatgpt_generate_RAM (
    input read_clk,
    input write_clk,
    input rst_n,
    input write_en,
    input [7:0] write_addr,
    input [3:0] write_data,
    input read_en,
    input [7:0] read_addr,
    output reg [3:0] read_data
);

reg [3:0] ram [0:7];

// Initialize RAM with all zeros
integer i;
initial begin
    for (i = 0; i < 8; i = i + 1) begin
        ram[i] = 4'b0000;
    end
end

// Synchronous read design
always @(posedge read_clk) begin
    if (read_en) begin
        read_data <= ram[read_addr];
    end
end

// Asynchronous write design
reg [7:0] write_addr_sync;
always @(posedge write_clk) begin
    if (rst_n == 0) begin
        write_addr_sync <= 8'b0;
    end else if (write_en) begin
        write_addr_sync <= write_addr;
        ram[write_addr_sync] <= write_data;
    end
end

endmodule