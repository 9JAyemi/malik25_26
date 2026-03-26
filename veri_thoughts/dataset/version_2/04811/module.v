
module Span12Mux_s0_h(I, s, O);
  input [11:0] I;
  input [2:0] s;
  output [11:0] O;

  assign O = (s == 3'b000) ? I :
            (s == 3'b001) ? I :
            (s == 3'b010) ? I :
            (s == 3'b011) ? I :
            (s == 3'b100) ? I :
            (s == 3'b101) ? I :
            (s == 3'b110) ? I : 12'b0;
endmodule