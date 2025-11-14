module single_port_RAM #(
  parameter n = 8 // number of bits in data_in and data_out
)(
  input [n-1:0] data_in,
  input [8-1:0] address,
  input write_en,
  input clk,
  output reg [n-1:0] data_out
);

parameter depth = 256; // depth of the RAM block (i.e., number of memory locations)

reg [n-1:0] memory [0:depth-1]; // define memory array

always @(posedge clk) begin
  if (write_en) begin
    memory[address] <= data_in; // write data to memory
  end
  else begin
    data_out <= memory[address]; // read data from memory
  end
end

endmodule