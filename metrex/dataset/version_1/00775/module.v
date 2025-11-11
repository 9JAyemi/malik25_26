
module Modulo (
  input [31:0] A,
  input [31:0] B,
  output reg [31:0] C
);

  wire signed [31:0] C_temp;
  assign C_temp = A % B;
  always @(*) begin
    if (B == 0) begin
      C <= 0;
    end else if (C_temp < 0) begin
      C <= C_temp + B;
    end else begin
      C <= C_temp;
    end
  end

endmodule