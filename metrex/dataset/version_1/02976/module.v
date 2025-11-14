module ram_block_dual_read_single_write (
    input [8:0] d0,
    input [8:0] addr0,
    input ce0,
    input we0,
    output reg [8:0] q0,
    input [8:0] addr1,
    input ce1,
    output reg [8:0] q1,
    input clk
);

    parameter DWIDTH = 8;
    parameter AWIDTH = 9;
    parameter MEM_SIZE = 512;

    reg [DWIDTH-1:0] ram [MEM_SIZE-1:0];

    always @(posedge clk) begin
        if (ce0) begin
            if (we0) begin
                ram[addr0] <= d0;
            end
            q0 <= ram[addr0];
        end
        if (ce1) begin
            q1 <= ram[addr1];
        end
    end

endmodule