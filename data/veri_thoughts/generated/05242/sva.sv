module bitwise_operators_sva #(
  parameter n = 8
) (
  input logic clk,
  input logic [n-1:0] a,
  input logic [n-1:0] b,
  input logic [n-1:0] and_out,
  input logic [n-1:0] or_out,
  input logic [n-1:0] xor_out,
  input logic [n-1:0] not_out
);

  // and_out must equal the bitwise AND of a and b.
  check_and_out_function: assert property (
    @(posedge clk) disable iff (1'b0) and_out == (a & b)
  );

  // or_out must equal the bitwise OR of a and b.
  check_or_out_function: assert property (
    @(posedge clk) disable iff (1'b0) or_out == (a | b)
  );

  // xor_out must equal the bitwise XOR of a and b.
  check_xor_out_function: assert property (
    @(posedge clk) disable iff (1'b0) xor_out == (a ^ b)
  );

  // not_out must equal the bitwise NOT of a.
  check_not_out_function: assert property (
    @(posedge clk) disable iff (1'b0) not_out == (~a)
  );

  // xor_out must match the OR-without-AND identity.
  check_xor_from_or_and: assert property (
    @(posedge clk) disable iff (1'b0) xor_out == (or_out & ~and_out)
  );

  // or_out must be reconstructable from and_out and xor_out.
  check_or_from_and_xor: assert property (
    @(posedge clk) disable iff (1'b0) or_out == (and_out | xor_out)
  );

  // and_out and xor_out cannot be high on the same bit.
  check_and_xor_mutex: assert property (
    @(posedge clk) disable iff (1'b0) (and_out & xor_out) == '0
  );

endmodule