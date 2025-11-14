
module memory #(
  parameter bits = 32,
  parameter words = 1024
)(
  input clk,
  input [9:0] addr,
  input [bits-1:0] data_in,
  output reg [bits-1:0] mem
);

  always @(posedge clk) begin
    if (addr < words) begin
      mem <= data_in;
    end
  end

endmodule