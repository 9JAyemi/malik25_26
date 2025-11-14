
module dual_port_RAM (
    input clk,
    input rst_n,
    input write_en,
    input [7:0] write_addr,
    input [3:0] write_data,
    input read_en,
    input [7:0] read_addr,
    output [3:0] read_data
);

    // Define the block RAM
    reg [3:0] ram [0:7];

    // Define the write and read ports
    reg [2:0] write_port;
    reg [2:0] read_port;
    reg [3:0] read_data_t;

    // Write operation
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            write_port <= 3'b000;
        end else if (write_en) begin
            write_port <= write_addr[2:0];
            ram[write_port] <= write_data;
        end
    end

    // Read operation
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            read_port <= 3'b000;
            read_data_t <= 4'h0;
        end else if (read_en) begin
            read_port <= read_addr[2:0];
            read_data_t <= ram[read_port];
        end
    end

    assign read_data = read_data_t;

endmodule