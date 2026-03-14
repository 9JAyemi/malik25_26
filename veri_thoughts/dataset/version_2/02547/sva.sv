module Bitwise_Or_sva (
  input logic CLK,
  input logic [31:0] in0,
  input logic [31:0] in1,
  input logic enable,
  input logic [31:0] out
);

  // When enable is HIGH, out equals bitwise OR of in0 and in1.
  check_or_when_enabled: assert property (
    @(posedge CLK) enable |-> (out == (in0 | in1))
  );

  // When enable is LOW, out is all zeros.
  check_zero_when_disabled: assert property (
    @(posedge CLK) !enable |-> (out == 32'h0)
  );

  // Output never has 1s where both inputs have 0s.
  check_no_spurious_ones: assert property (
    @(posedge CLK) (out & ~(in0 | in1)) == 32'h0
  );

  // When enabled, output includes all 1-bits present in either input.
  check_out_superset_inputs_when_enabled: assert property (
    @(posedge CLK) enable |-> (((in0 | in1) & ~out) == 32'h0)
  );

  // When enabled and in1 is zero, out equals in0.
  check_in1_zero_passthrough: assert property (
    @(posedge CLK) (enable && (in1 == 32'h0)) |-> (out == in0)
  );

  // When enabled and in0 is zero, out equals in1.
  check_in0_zero_passthrough: assert property (
    @(posedge CLK) (enable && (in0 == 32'h0)) |-> (out == in1)
  );

  // When enabled and inputs are equal, out equals that common value.
  check_equal_inputs_passthrough: assert property (
    @(posedge CLK) (enable && (in0 == in1)) |-> (out == in0)
  );

  // When enabled, out is a superset of each input bitwise.
  check_bitwise_inclusion_when_enabled: assert property (
    @(posedge CLK) enable |-> ((out | in0) == out && (out | in1) == out)
  );

endmodule