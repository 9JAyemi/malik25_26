module fifo_buffer (
  input wire clk,
  input wire aclr,
  input wire [DATA_WIDTH-1:0] din,
  output reg [DATA_WIDTH-1:0] dout
);

  parameter DATA_WIDTH = 8;
  parameter DEPTH = 4;

  reg [DATA_WIDTH-1:0] mem [DEPTH-1:0];
  reg [DATA_WIDTH-1:0] temp;

  integer i;

  always @(posedge clk or posedge aclr) begin
    if (aclr) begin
      for (i = 0; i < DEPTH; i = i + 1) begin
        mem[i] <= 0;
      end
      dout <= 0;
    end
    else begin
      for (i = 0; i < DEPTH-1; i = i + 1) begin
        mem[i+1] <= mem[i];
      end
      mem[0] <= din;
      dout <= mem[DEPTH-1];
    end
  end

endmodule