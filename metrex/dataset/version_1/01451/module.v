module multiply_complex #(parameter WIDTH = 32)
  (
    input wire clk,
    input wire rst_n,
    input wire signed [WIDTH-1:0] x,
    input wire signed [WIDTH-1:0] y,
    output reg signed [2*WIDTH-1:0] z
  );

  reg signed [2*WIDTH-1:0] temp_z;

  always @ (posedge clk)
  begin
    if (~rst_n)
    begin
      temp_z <= 0;
      z <= 0;
    end
    else
    begin
      temp_z <= x * y;
      z <= temp_z >> WIDTH;
    end
  end

endmodule