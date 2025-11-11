module RegisterAdd_parameterized8
   (
    input clk,
    input rst,
    input load,
    input [7:0] D1,
    input [7:0] D2,
    output reg [7:0] Q
  );

  reg [7:0] reg1;
  reg [7:0] reg2;

  always @(posedge clk) begin
    if (rst) begin
      reg1 <= 8'b0;
      reg2 <= 8'b0;
    end else if (load) begin
      reg1 <= D1;
      reg2 <= D2;
    end else begin
      Q <= reg1 + reg2;
    end
  end
endmodule
