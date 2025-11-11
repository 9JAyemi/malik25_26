module Multiplexer #(parameter WIDTH = 1) (
  input wire ctrl,
  input wire [WIDTH-1:0] D0,
  input wire [WIDTH-1:0] D1,
  output reg [WIDTH-1:0] S
);

  always @(*) begin
    if (ctrl == 1'b0) begin
      S <= D0;
    end else begin
      S <= D1;
    end
  end

endmodule