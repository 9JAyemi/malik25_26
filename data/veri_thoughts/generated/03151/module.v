module Multiplexer_AC__parameterized137 (
  input ctrl,
  input [0:0] D0,
  input [0:0] D1,
  output [0:0] S
);

  wire [0:0] wD0;
  wire [0:0] wD1;
  wire [0:0] wS;

  assign wD0 = D0;
  assign wD1 = D1;
  
  assign S[0] = wS[0];
  
  assign wS = (ctrl) ? D1 : D0;

endmodule