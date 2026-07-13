module bitwise_operators_sva #(
  parameter n = 4 // number of bits in A and B
) (
  input [n-1:0] A,
  input [n-1:0] B,
  input [n-1:0] and_res,
  input [n-1:0] or_res,
  input [n-1:0] xor_res,
  input [n-1:0] not_res
);

  // Combinational logic, so use @(posedge clk)
  // No clock or reset signals present in the RTL

  // Check if AND result is correct
  and_result: assert property (
    @(posedge clk) $stable(A) && $stable(B) |-> (and_res == (A & B))
  ) else $error("AND result is incorrect");

  // Check if OR result is correct
  or_result: assert property (
    @(posedge clk) $stable(A) && $stable(B) |-> (or_res == (A | B))
  ) else $error("OR result is incorrect");

  // Check if XOR result is correct
  xor_result: assert property (
    @(posedge clk) $stable(A) && $stable(B) |-> (xor_res == (A ^ B))
  ) else $error("XOR result is incorrect");

  // Check if NOT result is correct
  not_result: assert property (
    @(posedge clk) $stable(A) |-> (not_res == (~A))
  ) else $error("NOT result is incorrect");

endmodule