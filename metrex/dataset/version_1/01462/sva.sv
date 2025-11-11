// SVA for vec_multiplier
// Bind into the DUT or include alongside
module vec_multiplier_sva (
  input clk, rst,
  input  signed [7:0]  vector1,
  input  signed [7:0]  vector2,
  input  signed [15:0] product
);

  default clocking cb @(posedge clk); endclocking

  // Track past-valid to safely use $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Functional correctness (1-cycle latency, sync reset)
  // product(t) == (rst(t-1) ? 0 : v1(t-1) * v2(t-1))
  assert property (past_valid |-> product
                   == ($past(rst) ? 16'sd0
                                  : $signed($past(vector1)) * $signed($past(vector2))))
    else $error("Functional mismatch: product != expected signed multiply or reset value");

  // Inputs should be known when used (cycle t-1 if not in reset)
  assert property (past_valid && !$past(rst) |-> !$isunknown({$past(vector1), $past(vector2)}))
    else $error("Unknown (X/Z) on inputs when sampled for multiply");

  // Product should never be X/Z after first cycle
  assert property (past_valid |-> !$isunknown(product))
    else $error("Unknown (X/Z) on product");

  // Sign correctness
  // Same-sign nonzero operands => positive product
  assert property (past_valid && !$past(rst)
                   && ($past(vector1) != 0) && ($past(vector2) != 0)
                   && ($past(vector1)[7] == $past(vector2)[7])
                   |-> product > 0)
    else $error("Sign error: same-sign operands should yield positive product");

  // Opposite-sign nonzero operands => negative product
  assert property (past_valid && !$past(rst)
                   && ($past(vector1) != 0) && ($past(vector2) != 0)
                   && ($past(vector1)[7] != $past(vector2)[7])
                   |-> product < 0)
    else $error("Sign error: opposite-sign operands should yield negative product");

  // Zero operand => zero product
  assert property (past_valid && !$past(rst)
                   && ( ($past(vector1) == 0) || ($past(vector2) == 0) )
                   |-> product == 0)
    else $error("Zero multiplicand should yield zero product");

  // Coverage
  // Reset forces product to 0 (hold and release)
  cover property (rst);
  cover property (rst ##1 rst);       // held reset
  cover property (rst ##1 !rst);      // release

  // Operand sign combinations and zero
  cover property (past_valid && !$past(rst) && ($past(vector1) == 0));
  cover property (past_valid && !$past(rst) && ($past(vector2) == 0));
  cover property (past_valid && !$past(rst) && ($past(vector1)[7] == 0) && ($past(vector2)[7] == 0)); // + * +
  cover property (past_valid && !$past(rst) && ($past(vector1)[7] == 1) && ($past(vector2)[7] == 1)); // - * -
  cover property (past_valid && !$past(rst) && ($past(vector1)[7] ^  $past(vector2)[7]));             // +/- mix

  // Extremes
  cover property (past_valid && !$past(rst) && $past(vector1) == 8'sd127  && $past(vector2) == 8'sd127);
  cover property (past_valid && !$past(rst) && $past(vector1) == -8'sd128 && $past(vector2) == -8'sd128);
  cover property (past_valid && !$past(rst) && $past(vector1) == -8'sd128 && $past(vector2) == 8'sd127);
  cover property (past_valid && !$past(rst) && $past(vector1) == 8'sd127  && $past(vector2) == -8'sd128);

endmodule

// Bind example:
// bind vec_multiplier vec_multiplier_sva sva (.*);