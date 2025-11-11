module blk_mem_gen #(parameter WIDTH = 8, parameter DEPTH = 256) (
    input wire clk,
    input wire [WIDTH-1:0] din,
    input wire we,
    input wire [WIDTH-1:0] addr,
    output wire [WIDTH-1:0] dout
);

  reg [WIDTH-1:0] mem [DEPTH-1:0];
  assign dout = mem[addr];

  always @(posedge clk) begin
    if (we) begin
      mem[addr] <= din;
    end
  end

endmodule