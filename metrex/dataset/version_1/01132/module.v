
module pipeline_registers #(
  parameter n = 4, // number of input signals
  parameter m = 2, // number of output signals
  parameter s = 3 // number of pipeline stages
)(
  input [n-1:0] in,
  output [m-1:0] out,
  input clk  // Clock signal
);


reg [n-1:0] stage1_reg;
reg [n-1:0] stage2_reg;
reg [n-1:0] stage3_reg;

always @ (posedge clk) begin
  stage1_reg <= in;
  stage2_reg <= stage1_reg;
  stage3_reg <= stage2_reg;
end


assign out = stage3_reg;

endmodule

