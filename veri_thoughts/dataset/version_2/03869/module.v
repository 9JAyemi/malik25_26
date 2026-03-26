
module Multiplexer_AC__parameterized128 (
  input ctrl,
  input [127:0] D0,
  input [127:0] D1,
  output [127:0] S
);

  assign S = ctrl ? D1 : D0;

endmodule
