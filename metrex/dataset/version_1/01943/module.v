module single_port_RAM (
  input clk,
  input write_en,
  input read_en,
  input [8*depth-1:0] address,
  input [data_width-1:0] data_in,
  output reg [data_width-1:0] data_out
);

parameter data_width = 8; // size of the data (in bits)
parameter depth = 256; // number of memory locations

// Define memory array
reg [data_width-1:0] memory [depth-1:0];

// Write operation
always @(posedge clk) begin
    if (write_en) begin
        memory[address] <= data_in;
    end
end

// Read operation
always @(posedge clk) begin
    if (read_en) begin
        data_out <= memory[address];
    end
end
endmodule