module MIB #(
  parameter data_width = 32 // width of the data bus
)(
  input clk,
  input reset,
  input enable,
  input [31:0] address,
  input [data_width-1:0] write_data,
  output reg [data_width-1:0] read_data
);

parameter memory_size = 1024; // size of the memory in bytes

reg [data_width-1:0] memory [memory_size/4-1:0]; // memory array

always @(posedge clk) begin
  if (reset) begin
    read_data <= 0;
  end else if (enable) begin
    if (write_data) begin
      memory[address/4] <= write_data;
    end
    read_data <= memory[address/4];
  end
end

endmodule