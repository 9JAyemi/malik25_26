```systemverilog
module Multiplexer_assertions #(parameter N=1)
   (clk,
    rst_n,
    ctrl,
    D0,
    D1,
    S);
  input logic clk;
  input logic rst_n;
  input logic ctrl;
  input logic [N-1:0] D0;
  input logic [N-1:0] D1;
  output logic [N-1:0] S;

  // At reset, the output S should be 0
  reset_output: assert property (
      @(posedge clk) disable iff (!rst_n) (S == 0)
  );

  // When ctrl is 0, S should be equal to D0
  select_D0: assert property (
      @(posedge clk) disable iff (!rst_n) (ctrl == 0) |-> (S == D0)
  );

  // When ctrl is 1, S should be equal to D1
  select_D1: assert property (
      @(posedge clk) disable iff (!rst_n) (ctrl == 1) |-> (S == D1)
  );

endmodule
```