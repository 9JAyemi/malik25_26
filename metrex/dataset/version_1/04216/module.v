module synchronous_ram (
    input [9:0] address,
    input [1:0] byteena,
    input clken,
    input clock,
    input [15:0] data,
    input wren,
    output reg [15:0] q
);

parameter RAM_DEPTH = 16; // Define RAM_DEPTH parameter

wire [15:0] sub_wire0;
reg [15:0] ram [0:RAM_DEPTH-1];
reg [3:0] addr; // Define addr as a register

always @(posedge clock) begin
    if(clken) begin
        if(wren) begin
            for(addr = 0; addr < RAM_DEPTH; addr = addr + 1) begin
                if(byteena[0]) begin
                    ram[address][7:0] <= data[7:0];
                end
                if(byteena[1]) begin
                    ram[address][15:8] <= data[15:8];
                end
            end
        end
        q <= ram[address];
    end
end

endmodule