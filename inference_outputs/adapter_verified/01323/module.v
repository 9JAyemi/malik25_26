
module Multiplexer #(parameter N=1)
   (ctrl,
    D0,
    D1,
    S);
  input ctrl;
  input [N-1:0]D0;
  input [N-1:0]D1;
  output [N-1:0]S;

  wire [N-1:0]D0;
  wire [N-1:0]D1;
  wire [N-1:0]S;
  wire ctrl;

  assign S = ctrl ? D1 : D0;
endmodule