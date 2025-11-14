
module MIB_DDR_SDRAM #(
  parameter DATA_WIDTH = 32, // width of the data bus
  parameter ADDR_WIDTH = 8 // width of the address bus
)(
  input clk,
  input rst,
  input we,
  input [ADDR_WIDTH-1:0] addr,
  input [DATA_WIDTH-1:0] din,
  output reg [DATA_WIDTH-1:0] dout
);

  reg [DATA_WIDTH-1:0] mem [2**ADDR_WIDTH-1:0];

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      dout <= 0;
    end else begin
      if (we) begin
        mem[addr] <= din;
      end else begin
        dout <= mem[addr];
      end
    end
  end

endmodule