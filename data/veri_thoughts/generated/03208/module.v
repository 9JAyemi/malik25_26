
module Span12Mux_s4_h(I, S, O);
  input [11:0] I;
  input [3:0] S;
  output O;

  wire [3:0] MuxOut;

  assign MuxOut[0] = (S == 4'b0000) ? I[0] : 1'b0;
  assign MuxOut[1] = (S == 4'b0001) ? I[1] : 1'b0;
  assign MuxOut[2] = (S == 4'b0010) ? I[2] : 1'b0;
  assign MuxOut[3] = (S == 4'b0011) ? I[3] : 1'b0;

  assign O = MuxOut[0] | MuxOut[1] | MuxOut[2] | MuxOut[3];

endmodule