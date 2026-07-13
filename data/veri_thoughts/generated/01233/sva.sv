module comparator_4bit_sva (
  input logic clk,
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [1:0] EQ_LT_GT
);

  // When A equals B, output must be 01.
  check_equal_encode: assert property (
    @(posedge clk) (A == B) |-> (EQ_LT_GT == 2'b01)
  );

  // When A is less than B, output must be 10.
  check_less_encode: assert property (
    @(posedge clk) (A < B) |-> (EQ_LT_GT == 2'b10)
  );

  // When A is greater than B, output must be 00.
  check_greater_encode: assert property (
    @(posedge clk) (A > B) |-> (EQ_LT_GT == 2'b00)
  );

  // Output 01 implies A equals B.
  check_equal_decode: assert property (
    @(posedge clk) (EQ_LT_GT == 2'b01) |-> (A == B)
  );

  // Output 10 implies A is less than B.
  check_less_decode: assert property (
    @(posedge clk) (EQ_LT_GT == 2'b10) |-> (A < B)
  );

  // Output 00 implies A is greater than B.
  check_greater_decode: assert property (
    @(posedge clk) (EQ_LT_GT == 2'b00) |-> (A > B)
  );

  // Output must never be 11.
  check_no_invalid_code: assert property (
    @(posedge clk) (EQ_LT_GT != 2'b11)
  );

  // If A and B are stable, output must be stable (pure combinational).
  check_output_stable_when_inputs_stable: assert property (
    @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(EQ_LT_GT)
  );

  // If output changes, at least one input must have changed.
  check_output_change_implies_input_change: assert property (
    @(posedge clk) $changed(EQ_LT_GT) |-> ($changed(A) || $changed(B))
  );

endmodule