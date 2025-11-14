// SVA for calculator
module calculator_sva (
  input logic        clk,
  input logic        rst,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic        op,
  input logic [7:0]  result
);

  // Async reset clears immediately
  property p_async_rst_clears;
    @(posedge rst) 1 |-> ##0 (result == 8'h00);
  endproperty
  assert property (p_async_rst_clears);

  // While reset is high, result holds 0 on each clk edge
  property p_rst_hold_zero;
    @(posedge clk) rst |-> (result == 8'h00);
  endproperty
  assert property (p_rst_hold_zero);

  // Functional correctness (single-cycle, truncated 8-bit math)
  property p_add_correct;
    @(posedge clk) disable iff (rst)
      (op == 1'b0) |-> ##0 (result == (a + b)[7:0]);
  endproperty
  assert property (p_add_correct);

  property p_sub_correct;
    @(posedge clk) disable iff (rst)
      (op == 1'b1) |-> ##0 (result == (a - b)[7:0]);
  endproperty
  assert property (p_sub_correct);

  // No X/Z on key signals when used
  property p_no_unknowns;
    @(posedge clk) disable iff (rst)
      !$isunknown({op, a, b, result});
  endproperty
  assert property (p_no_unknowns);

  // -----------------
  // Coverage
  // -----------------
  // Reset activity
  cover property (@(posedge rst) 1);
  cover property (@(negedge rst) 1);

  // Exercise both operations
  cover property (@(posedge clk) disable iff (rst) (op==0) ##0 (result == (a+b)[7:0]));
  cover property (@(posedge clk) disable iff (rst) (op==1) ##0 (result == (a-b)[7:0]));

  // Addition overflow (carry-out) and wrap behavior
  cover property (@(posedge clk) disable iff (rst)
    (op==0 && ({1'b0,a}+{1'b0,b})[8]) ##0 (result < a));

  // Subtraction underflow (borrow) and wrap behavior
  cover property (@(posedge clk) disable iff (rst)
    (op==1 && ({1'b0,a} < {1'b0,b})) ##0 (result > a));

  // Exact zero result on subtraction when a==b
  cover property (@(posedge clk) disable iff (rst)
    (op==1 && (a==b)) ##0 (result==8'h00));

  // Toggle operation usage
  cover property (@(posedge clk) disable iff (rst) $changed(op));

endmodule

// Bind into DUT
bind calculator calculator_sva i_calculator_sva (
  .clk   (clk),
  .rst   (rst),
  .a     (a),
  .b     (b),
  .op    (op),
  .result(result)
);