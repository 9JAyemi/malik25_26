```systemverilog
module bitwise_operators_sva #(
  parameter n = 8 // number of bits in each input signal and output signal
) (
  input [n-1:0] a,
  input [n-1:0] b,
  input [n-1:0] and_out,
  input [n-1:0] or_out,
  input [n-1:0] xor_out,
  input [n-1:0] not_out
);

  // Combinational logic, so use @(posedge clk) for assertions

  // and_out should be the result of a bitwise AND of a and b
  bitwise_and_check: assert property (
    @(posedge clk) disable iff (!reset_n) (and_out == (a & b))
  );

  // or_out should be the result of a bitwise OR of a and b
  bitwise_or_check: assert property (
    @(posedge clk) disable iff (!reset_n) (or_out == (a | b))
  );

  // xor_out should be the result of a bitwise XOR of a and b
  bitwise_xor_check: assert property (
    @(posedge clk) disable iff (!reset_n) (xor_out == (a ^ b))
  );

  // not_out should be the result of a bitwise NOT of a
  bitwise_not_check: assert property (
    @(posedge clk) disable iff (!reset_n) (not_out == (~a))
  );

endmodule
```