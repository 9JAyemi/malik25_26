
module Span12Mux_v0(I, S, O);
  input [11:0] I;
  input [3:0] S;
  output reg [11:0] O;

  always @ (S or I) begin
    case (S)
      4'b0000: O <= I;
      4'b0001: O <= I;
      4'b0010: O <= I;
      4'b0011: O <= I;
      4'b0100: O <= I;
      4'b0101: O <= I;
      4'b0110: O <= I;
      4'b0111: O <= I;
      4'b1000: O <= I;
      4'b1001: O <= I;
      4'b1010: O <= I;
      4'b1011: O <= I;
      default: O <= 0;
    endcase
  end
endmodule