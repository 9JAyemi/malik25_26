module multiplexer #(parameter n=1)(
  input ctrl,
  input [n-1:0] D0,
  input [n-1:0] D1,
  output [n-1:0] S
);

  assign S = ctrl ? D1 : D0;

endmodule