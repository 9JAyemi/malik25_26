
module MemTextures(a, clk, spo);
  input [7:0] a;
  input clk;
  output [91:0] spo;

  reg [31:0] mem[255:0];
  reg [91:0] spo;  // Change to reg

  always @(posedge clk) begin
    spo <= {a, mem[a]};
  end

endmodule
