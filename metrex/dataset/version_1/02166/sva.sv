// SVA for module: calculator
// Checks 1-cycle latency functional correctness, illegal divide-by-zero, and provides focused coverage.

module calculator_sva
(
  input logic        clk,
  input logic [7:0]  a, b,
  input logic [1:0]  op,
  input logic [7:0]  result
);

  default clocking cb @(posedge clk); endclocking
  localparam logic [1:0] ADD=2'b00, SUB=2'b01, MUL=2'b10, DIV=2'b11;

  // Basic sanity
  ap_op_known:         assert property (!$isunknown(op));
  ap_no_div_by_zero:   assert property (op==DIV |-> b!=0);

  // Functional correctness (1-cycle latency)
  ap_add: assert property (op==ADD |-> ##1 result == (a + b)[7:0]);
  ap_sub: assert property (op==SUB |-> ##1 result == (a - b)[7:0]);
  ap_mul: assert property (op==MUL |-> ##1 result == (a * b)[7:0]);
  ap_div: assert property (op==DIV && b!=0 |-> ##1 result == (a / b));

  // Coverage: op usage
  cp_add: cover property (op==ADD);
  cp_sub: cover property (op==SUB);
  cp_mul: cover property (op==MUL);
  cp_div: cover property (op==DIV && b!=0);

  // Coverage: stress corners
  cp_add_overflow: cover property (op==ADD && ({1'b0,a}+{1'b0,b})[8]);  // carry-out
  cp_sub_underflow: cover property (op==SUB && (a < b));                // borrow
  cp_mul_overflow: cover property (op==MUL && ((a*b) > 16'h00FF));      // upper bits non-zero
  cp_div_rem_nonzero: cover property (op==DIV && b!=0 && ((a % b) != 0));
  cp_div_by_zero_attempt: cover property (op==DIV && b==0);             // negative test stimulus

endmodule

// Bind into DUT
bind calculator calculator_sva u_calculator_sva(.clk(clk), .a(a), .b(b), .op(op), .result(result));