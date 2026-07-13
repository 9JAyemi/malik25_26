module comparator_3bit_sva (
  input logic clk,          // Sampling clock for assertions (DUT has no clock/reset)
  input logic [2:0] A,
  input logic [2:0] B,
  input logic eq,
  input logic gt
);

  ///// Functional correctness /////
  // When A == B, eq=1 and gt=0.
  check_equal_case: assert property (
    @(posedge clk) (A == B) |-> (eq == 1'b1 && gt == 1'b0)
  );

  // When A > B, gt=1 and eq=0.
  check_greater_case: assert property (
    @(posedge clk) (A > B) |-> (gt == 1'b1 && eq == 1'b0)
  );

  // When A < B, eq=0 and gt=0.
  check_less_case: assert property (
    @(posedge clk) (A < B) |-> (eq == 1'b0 && gt == 1'b0)
  );

  // eq high implies A == B.
  check_eq_implies_equal: assert property (
    @(posedge clk) eq |-> (A == B)
  );

  // gt high implies A > B.
  check_gt_implies_greater: assert property (
    @(posedge clk) gt |-> (A > B)
  );

  // eq and gt are never both 1.
  check_outputs_mutex: assert property (
    @(posedge clk) !(eq && gt)
  );

  ///// Combinational consistency /////
  // If A and B are unchanged, eq and gt remain unchanged.
  check_stable_when_inputs_stable: assert property (
    @(posedge clk) ((A == $past(A)) && (B == $past(B))) |-> ((eq == $past(eq)) && (gt == $past(gt)))
  );

  // If eq or gt changes, then A or B must have changed.
  check_output_change_implies_input_change: assert property (
    @(posedge clk) ($changed(eq) || $changed(gt)) |-> ($changed(A) || $changed(B))
  );

endmodule