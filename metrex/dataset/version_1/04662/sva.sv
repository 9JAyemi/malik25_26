// SVA for calculator
module calculator_sva (
  input logic        clk,
  input logic        op,
  input logic [3:0]  num1,
  input logic [3:0]  num2,
  input logic [3:0]  result
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // No X/Z on inputs and output
  assert property (cb !$isunknown({op, num1, num2}));
  assert property (cb past_valid |-> !$isunknown(result));

  // Functional correctness: 1-cycle latency, modulo-16 arithmetic
  assert property (cb past_valid && !$isunknown($past({op, num1, num2})) |->
                   result == ( ($past(op)==1'b0)
                               ? (($past(num1)+$past(num2)) & 4'hF)
                               : (($past(num1)-$past(num2)) & 4'hF) ));

  // Coverage: exercise both ops and wrap/borrow corner cases
  cover property (cb past_valid && $past(op)==1'b0); // add path
  cover property (cb past_valid && $past(op)==1'b1); // sub path
  cover property (cb past_valid && $past(op)==1'b0 &&
                         ($past(num1)+$past(num2)) < 16);   // add no carry
  cover property (cb past_valid && $past(op)==1'b0 &&
                         ($past(num1)+$past(num2)) >= 16);  // add carry
  cover property (cb past_valid && $past(op)==1'b1 &&
                         $past(num1) >= $past(num2));       // sub no borrow
  cover property (cb past_valid && $past(op)==1'b1 &&
                         $past(num1) <  $past(num2));       // sub borrow
  cover property (cb past_valid && $past(op)==1'b0 &&
                         $past(num1)==4'hF && $past(num2)==4'hF &&
                         result==4'hE); // 15+15 wraps to 14
  cover property (cb past_valid && $past(op)==1'b1 &&
                         $past(num1)==4'h0 && $past(num2)==4'h1 &&
                         result==4'hF); // 0-1 wraps to 15
endmodule

bind calculator calculator_sva sva_i(.clk(clk), .op(op), .num1(num1), .num2(num2), .result(result));