```systemverilog
module Comparator_assertions (
  input logic [3:0] in1,
  input logic [3:0] in2,
  input logic [1:0] out
);
    ///// Comparator logic /////
    // out should be 01 when in1 > in2
    greater_than: assert property (
        @(posedge clk) disable iff (!rst_n) (in1 > in2) |-> (out == 2'b01)
    );
    // out should be 00 when in1 == in2
    equal: assert property (
        @(posedge clk) disable iff (!rst_n) (in1 == in2) |-> (out == 2'b00)
    );
    // out should be 10 when in1 < in2
    less_than: assert property (
        @(posedge clk) disable iff (!rst_n) (in1 < in2) |-> (out == 2'b10)
    );
endmodule
```