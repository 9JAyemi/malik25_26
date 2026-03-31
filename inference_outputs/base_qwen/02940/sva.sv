```systemverilog
module add_sub_sva (
  input logic clk,
  input logic reset,
  input logic operation,
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] result
);

  // Reset behavior: result should be 0 after reset
  reset_behavior: assert property (
    @(posedge clk) disable iff (!reset) result == 4'b0000
  );

  // Addition operation: result should be A + B when operation is 0
  add_operation: assert property (
    @(posedge clk) disable iff (!reset) (operation == 0) |-> result == A + B
  );

  // Subtraction operation: result should be A - B when operation is 1
  sub_operation: assert property (
    @(posedge clk) disable iff (!reset) (operation == 1) |-> result == A - B
  );

endmodule
```