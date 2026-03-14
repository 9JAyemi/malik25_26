
module Mux_3x1
   (ctrl,
    D0,
    D1,
    D2,
    S);
  input [1:0] ctrl;
  input [7:0] D0;
  input [7:0] D1;
  input [7:0] D2;
  output [7:0] S;

  reg [7:0] S;

  always @ (*) begin
    case (ctrl)
      2'b00: S = D0;
      2'b01: S = D1;
      2'b10: S = D2;
      default: S = 8'b0;
    endcase
  end

endmodule