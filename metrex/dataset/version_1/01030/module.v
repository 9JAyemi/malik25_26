
module bytewrite_ram_32bits (
    input clk,
    input [3:0] we,
    input [11:0] addr,
    input [31:0] din,
    output [31:0] dout
);

    parameter SIZE = 1024;
    parameter ADDR_WIDTH = 12;
    parameter filename = "code.hex";
    
    localparam COL_WIDTH = 8;
    localparam NB_COL = 4;
    
    reg [31:0] RAM [SIZE-1:0];
    
    integer _i;
    
    wire [11:0] addr_dly;
    reg [31:0] dout_int;
    
    initial begin
        for(_i=0; _i<SIZE; _i=(_i+1)) begin
            RAM[_i] = 32'd0;
        end
    end
    
    always @(posedge clk) begin
        dout_int <= RAM[addr];
    end
    
    assign dout = dout_int;
    
    always @(posedge clk) begin
        if (we[0]) begin
            RAM[addr][7:0] <= din[7:0];
        end
        if (we[1]) begin
            RAM[addr][15:8] <= din[15:8];
        end
        if (we[2]) begin
            RAM[addr][23:16] <= din[23:16];
        end
        if (we[3]) begin
            RAM[addr][31:24] <= din[31:24];
        end
    end
    
endmodule