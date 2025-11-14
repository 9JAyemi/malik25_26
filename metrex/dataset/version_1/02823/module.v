
module dual_port_ram(
    input clk,
    input [15:0] data_in,
    input [10:0] write_addr,
    input write_en,
    input [10:0] read_addr,
    input read_en,
    output reg [15:0] data_out
);

    // Instantiate a generic dual-port RAM model
    reg [15:0] ram[0:2047];

    always @(posedge clk) begin
        if (write_en) begin
            ram[write_addr] <= data_in;
        end
        if (read_en) begin
            data_out <= ram[read_addr];
        end
    end

endmodule
