module memory(clk, we, addr, din, dout);

  parameter MEM_SIZE = 4096;
  parameter ADDR_WIDTH = 12;
  parameter DATA_WIDTH = 12;

  input clk;
  input we;
  input [ADDR_WIDTH-1:0] addr;
  input [DATA_WIDTH-1:0] din;
  output reg [DATA_WIDTH-1:0] dout;

  reg [DATA_WIDTH-1:0] mem [0:MEM_SIZE-1];

  always @(posedge clk) begin
    if (we) begin
      mem[addr] <= din;
    end else begin
      dout <= mem[addr];
    end
  end

endmodule