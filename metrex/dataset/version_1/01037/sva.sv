// SVA for calculator: concise, high-quality checks + focused coverage.
// Bind this module to the DUT to monitor combinational correctness.

module calculator_sva(input [7:0] num1, input [7:0] num2, input [1:0] op, input [7:0] result);
  localparam ADD=2'b00, SUB=2'b01, MUL=2'b10, DIV=2'b11;

  // Helper full-precision calcs for coverage
  logic [8:0]  add_full, sub_full;
  logic [15:0] mul_full;
  always_comb begin
    add_full = {1'b0,num1} + {1'b0,num2};
    sub_full = {1'b0,num1} - {1'b0,num2};
    mul_full = num1 * num2;
  end

  // Inputs must be known (prevents X-propagation masking issues)
  assert property (@(num1 or num2 or op) ##0 !$isunknown({op,num1,num2}))
    else $error("calculator: X/Z on inputs");

  // Result must be known unless divide-by-zero is requested
  assert property (@(num1 or num2 or op or result) (op!=DIV || num2!=0) |-> ##0 !$isunknown(result))
    else $error("calculator: X/Z on result without div-by-zero");

  // Define behavior per operation (0-delay settle check)
  assert property (@(num1 or num2 or op) (op==ADD) |-> ##0 result == (num1 + num2))
    else $error("calculator: add mismatch");
  assert property (@(num1 or num2 or op) (op==SUB) |-> ##0 result == (num1 - num2))
    else $error("calculator: sub mismatch");
  assert property (@(num1 or num2 or op) (op==MUL) |-> ##0 result == (num1 * num2)[7:0])
    else $error("calculator: mul mismatch (LSB truncation)");
  assert property (@(num1 or num2 or op) (op==DIV && num2!=0) |-> ##0 result == (num1 / num2))
    else $error("calculator: div mismatch");

  // Optional policy: flag divide-by-zero as an error and ensure X on result if it occurs
  assert property (@(num1 or num2 or op) !(op==DIV && num2==0))
    else $error("calculator: divide-by-zero requested");
  assert property (@(num1 or num2 or op) (op==DIV && num2==0) |-> ##0 $isunknown(result))
    else $error("calculator: div-by-zero should yield X result");

  // Functional coverage: exercise each op and key corner cases
  cover property (@(num1 or num2 or op) (op==ADD));
  cover property (@(num1 or num2 or op) (op==SUB));
  cover property (@(num1 or num2 or op) (op==MUL));
  cover property (@(num1 or num2 or op) (op==DIV && num2!=0));
  cover property (@(num1 or num2 or op) (op==DIV && num2==0));               // attempt div0 seen
  cover property (@(num1 or num2 or op) (op==ADD && add_full[8]));           // add overflow
  cover property (@(num1 or num2 or op) (op==SUB && sub_full[8]));           // sub borrow
  cover property (@(num1 or num2 or op) (op==MUL && mul_full[15:8]!=0));     // mul overflow
  cover property (@(num1 or num2 or op) (op==DIV && num2!=0 && (num1%num2)!=0)); // div remainder
endmodule

bind calculator calculator_sva u_calculator_sva(.num1(num1), .num2(num2), .op(op), .result(result));