module mux #
  (
    parameter WIDTH = 1
  )
  (
    input wire ctrl,
    input wire [WIDTH-1:0] D0,
    input wire [WIDTH-1:0] D1,
    output wire [WIDTH-1:0] S
  );

  assign S = ctrl ? D1 : D0;

endmodule