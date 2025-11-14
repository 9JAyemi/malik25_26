
module spram_interface (
    input clk,
    input [15:0] wdata,
    output reg [15:0] rdata,
    input [7:0] addr,
    input WE
);

    // SPRAM instance with initial values
    
    reg [15:0] ram [0:255];

    // Set initial values
    initial begin
        ram[0] = 16'h1234;
        ram[1] = 16'h5678;
        ram[2] = 16'habcd;
        ram[3] = 16'h0000;
        ram[4] = 16'hffff;
        ram[5] = 16'hffff;
        ram[6] = 16'hffff;
        ram[7] = 16'hffff;
        ram[8] = 16'h0000;
        ram[9] = 16'h0000;
        ram[10] = 16'h0000;
        ram[11] = 16'h0000;
        ram[12] = 16'h0123;
        ram[13] = 16'h4567;
        ram[14] = 16'h89ab;
        ram[15] = 16'hcdef;
    end

    // Read and write operations
    always @(posedge clk) begin
        if (WE) begin
            ram[addr] <= wdata;
        end
        rdata <= ram[addr];
    end

endmodule
