module bitwise_operator_sva (
  input logic in1,
  input logic in2,
  input logic out_AND,
  input logic out_OR,
  input logic out_XOR,
  input logic out_NOT
);

  ///// Combinational definitions /////
  // AND output equals in1 & in2.
  check_and_definition: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      out_AND == (in1 & in2)
  );

  // OR output equals in1 | in2.
  check_or_definition: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      out_OR == (in1 | in2)
  );

  // XOR output equals in1 ^ in2.
  check_xor_definition: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      out_XOR == (in1 ^ in2)
  );

  // NOT output equals ~in1.
  check_not_definition: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      out_NOT == (~in1)
  );

  ///// Logical relationships implied by the RTL /////
  // If AND is 1 then OR must be 1.
  check_and_implies_or: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      out_AND |-> out_OR
  );

  // If OR is 0 then both AND and XOR are 0.
  check_or_zero_implies_and_xor_zero: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      (out_OR == 1'b0) |-> ((out_AND == 1'b0) && (out_XOR == 1'b0))
  );

  // XOR equals OR ANDed with NOT(AND).
  check_xor_equals_or_and_not_and: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      out_XOR == (out_OR & ~out_AND)
  );

  // AND and XOR cannot both be 1.
  check_and_xor_mutex: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      !(out_AND && out_XOR)
  );

  // When in2 is 0: AND=0, OR=in1, XOR=in1.
  check_in2_zero_behaviors: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      (in2 == 1'b0) |-> ((out_AND == 1'b0) && (out_OR == in1) && (out_XOR == in1))
  );

  // When in2 is 1: AND=in1, OR=1, XOR=NOT(in1).
  check_in2_one_behaviors: assert property (
    @(posedge in1 or negedge in1 or posedge in2 or negedge in2)
      (in2 == 1'b1) |-> ((out_AND == in1) && (out_OR == 1'b1) && (out_XOR == out_NOT))
  );

endmodule