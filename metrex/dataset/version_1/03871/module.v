module blk_mem_gen #(parameter DATA_WIDTH = 8, ADDR_WIDTH = 8, INIT_FILE = "", INIT_HEX = 0, RAM_STYLE = "block") (
    input wire clk,
    input wire rst,
    input wire we,
    input wire [ADDR_WIDTH-1:0] addr,
    input wire [DATA_WIDTH-1:0] din,
    output reg [DATA_WIDTH-1:0] dout
);

    // Declare internal signals
    reg [DATA_WIDTH-1:0] mem [0:(1<<ADDR_WIDTH)-1];

    // Initialize memory from file, if specified
    initial begin
        if (INIT_FILE != "") begin
            $readmemh(INIT_FILE, mem);
        end
    end

    // Read operation
    always @ (posedge clk) begin
        if (we) begin
            mem[addr] <= din;
        end
        dout <= mem[addr];
    end

endmodule