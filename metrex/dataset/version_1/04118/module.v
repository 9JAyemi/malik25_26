
module onchip_trace_mem (
  input clk, reset, reset_req, clken, chipselect, write,
  input [8:0] address, byteenable,
  input [63:0] writedata,
  output reg [63:0] readdata
);

  parameter INIT_FILE = "";
  parameter WIDTH = 64;
  parameter DEPTH = 512;
  parameter ADDR_WIDTH = 9;
  parameter BYTE_WIDTH = 8;

  reg [WIDTH-1:0] mem [0:DEPTH-1];

  wire wren = chipselect & write;

  wire clocken0;
  assign clocken0 = clken & ~reset_req;

  initial begin
    if (INIT_FILE != "") begin
      $readmemb(INIT_FILE, mem);
    end
  end

  always @(posedge clk) begin
    if (wren) begin
      mem[address] <= writedata;
    end
    readdata <= mem[address];
  end

endmodule