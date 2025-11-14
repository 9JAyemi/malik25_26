
module mux #(
    parameter WIDTH = 1
)(
  input ctrl,
  input [WIDTH-1:0] D0,
  input [WIDTH-1:0] D1,
  output reg [WIDTH-1:0] S
);

  // Specify the width of the data signals as a generic argument

  always @(*) begin
    case (ctrl)
      1'b0: S = D0;
      1'b1: S = D1;
      default: S = 0; // Fixed the default case to output 0.
    endcase
  end

endmodule
