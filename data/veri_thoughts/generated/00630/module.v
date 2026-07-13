module Multiplexer_AC__parameterized50
   #(parameter WIDTH = 1)
   (ctrl,
    D0,
    D1,
    S);
  input ctrl;
  input [WIDTH-1:0]D0;
  input [WIDTH-1:0]D1;
  output [WIDTH-1:0]S;

  wire [WIDTH-1:0]S;

  assign S = (ctrl == 1'b0) ? D0 : D1;
endmodule