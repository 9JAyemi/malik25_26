module comparator_sva #(
  parameter int n = 8
)(
  input logic CLK,
  input logic [n-1:0] in1,
  input logic [n-1:0] in2,
  input logic eq,
  input logic gt,
  input logic lt
);

  // eq is 1 iff all bits of in1 and in2 are equal.
  check_eq_function: assert property (
    @(posedge CLK) eq == (in1 == in2)
  );

  // gt is 1 iff there exists a bit where in1=1 and in2=0.
  check_gt_function: assert property (
    @(posedge CLK) gt == (|(in1 & ~in2))
  );

  // lt is 1 iff there exists a bit where in2=1 and in1=0.
  check_lt_function: assert property (
    @(posedge CLK) lt == (|(in2 & ~in1))
  );

  // eq implies neither gt nor lt is asserted.
  check_eq_blocks_gt_lt: assert property (
    @(posedge CLK) eq |-> (!gt && !lt)
  );

  // If inputs differ, at least one of gt or lt must be asserted.
  check_ineq_implies_flag: assert property (
    @(posedge CLK) (in1 != in2) |-> (gt || lt)
  );

  // If either gt or lt is asserted, inputs must differ.
  check_flag_implies_ineq: assert property (
    @(posedge CLK) (gt || lt) |-> (in1 != in2)
  );

  // eq is the logical complement of (gt || lt).
  check_eq_complements_flags: assert property (
    @(posedge CLK) eq == !(gt || lt)
  );

endmodule