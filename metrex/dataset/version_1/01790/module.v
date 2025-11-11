
module Multiplexer_AC__parameterized133 (
  input ctrl,
  input [0:0] D0,
  input [0:0] D1,
  output [0:0] S
);

  wire [0:0] wD0;
  wire [0:0] wD1;
  wire [0:0] wS;
  wire wCtrl;

  // LUT3 with initial value of 8'hB8
  assign wS = ctrl ? D0 : D1;
  assign S = wS;

endmodule