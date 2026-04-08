module Mux_3x1_W11 (ctrl, D0, D1, D2, S);
  input [1:0] ctrl;
  input [10:0] D0;
  input [10:0] D1;
  input [10:0] D2;
  output reg [10:0] S;

  // Implement the 3x1 multiplexer using Verilog
  always @* begin
    case(ctrl)
      2'b00: S = D0;
      2'b01: S = D1;
      2'b10: S = D2;
      default: S = 11'b0; // Undefined behavior
    endcase
  end

endmodule