// SVA for SimpleCalculator
module SimpleCalculator_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       op,
  input  logic [3:0] result
);

  // Functional equivalence (combinational correctness)
  // Evaluate after updates (##0) on any relevant change
  assert property (@(a or b or op or result)
                   1'b1 |-> ##0 (result == (op ? (a - b) : (a + b))))
    else $error("Functional mismatch: result != (op ? a-b : a+b)");

  // No spurious output changes when inputs are stable
  assert property (@(a or b or op or result)
                   $stable({a,b,op}) |-> $stable(result))
    else $error("Output changed without input change");

  // X/Z checks: inputs known, and if inputs known then output known
  assert property (@(a or b or op or result)
                   !$isunknown({a,b,op}))
    else $error("Inputs contain X/Z");
  assert property (@(a or b or op or result)
                   (!$isunknown({a,b,op})) |-> !$isunknown(result))
    else $error("Output X/Z with known inputs");

  // Coverage
  // - Both ops seen
  cover property (@(a or b or op) (op == 1'b0));
  cover property (@(a or b or op) (op == 1'b1));
  // - Addition overflow/no-overflow
  cover property (@(a or b or op) (op==1'b0) &&  ({1'b0,a}+{1'b0,b})[4]);
  cover property (@(a or b or op) (op==1'b0) && !({1'b0,a}+{1'b0,b})[4]);
  // - Subtraction underflow/no-underflow
  cover property (@(a or b or op) (op==1'b1) && (a <  b));
  cover property (@(a or b or op) (op==1'b1) && (a >= b));

endmodule

// Bind to DUT
bind SimpleCalculator SimpleCalculator_sva u_simplecalculator_sva (
  .a(a), .b(b), .op(op), .result(result)
);