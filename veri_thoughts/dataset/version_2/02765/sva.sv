module bitwise_operators_sva (
  input logic CLK,
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic [7:0] out_and,
  input logic [7:0] out_or,
  input logic [7:0] out_xor,
  input logic [7:0] out_not
);

  // out_and equals bitwise AND of inputs.
  check_out_and_function: assert property (
    @(posedge CLK) out_and == (in1 & in2)
  );

  // out_or equals bitwise OR of inputs.
  check_out_or_function: assert property (
    @(posedge CLK) out_or == (in1 | in2)
  );

  // out_xor equals bitwise XOR of inputs.
  check_out_xor_function: assert property (
    @(posedge CLK) out_xor == (in1 ^ in2)
  );

  // out_not equals bitwise NOT of in1.
  check_out_not_function: assert property (
    @(posedge CLK) out_not == ~in1
  );

  // De Morgan for OR: a|b == ~(~a & ~b).
  check_or_demorgan: assert property (
    @(posedge CLK) out_or == ~(~in1 & ~in2)
  );

  // De Morgan for AND: a&b == ~(~a | ~b).
  check_and_demorgan: assert property (
    @(posedge CLK) out_and == ~(~in1 | ~in2)
  );

  // OR equals (AND | XOR) for same operands.
  check_or_is_and_or_xor: assert property (
    @(posedge CLK) out_or == (out_and | out_xor)
  );

  // XOR equals OR AND NOT(AND) for same operands.
  check_xor_is_or_andnot_and: assert property (
    @(posedge CLK) out_xor == (out_or & ~out_and)
  );

  // AND and XOR are bitwise disjoint.
  check_and_xor_mutex: assert property (
    @(posedge CLK) (out_and & out_xor) == '0
  );

  // in1 and its complement are bitwise disjoint.
  check_in1_out_not_mutex: assert property (
    @(posedge CLK) (in1 & out_not) == '0
  );

  // in1 XOR ~in1 yields all ones.
  check_in1_xor_out_not_allones: assert property (
    @(posedge CLK) (in1 ^ out_not) == 8'hFF
  );

  // If out_and changes, at least one input changed.
  check_out_and_change_has_input_change: assert property (
    @(posedge CLK) $changed(out_and) |-> ($changed(in1) || $changed(in2))
  );

  // If out_or changes, at least one input changed.
  check_out_or_change_has_input_change: assert property (
    @(posedge CLK) $changed(out_or) |-> ($changed(in1) || $changed(in2))
  );

  // If out_xor changes, at least one input changed.
  check_out_xor_change_has_input_change: assert property (
    @(posedge CLK) $changed(out_xor) |-> ($changed(in1) || $changed(in2))
  );

  // If out_not changes, in1 changed.
  check_out_not_change_has_in1_change: assert property (
    @(posedge CLK) $changed(out_not) |-> $changed(in1)
  );

endmodule