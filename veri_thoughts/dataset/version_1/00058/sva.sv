// SVA checker for calculator. Bind this to the DUT.
// Focuses on functional correctness, X-propagation, and key corner-case coverage.

module calculator_sva (
  input logic [7:0] num1,
  input logic [7:0] num2,
  input logic [1:0] op,
  input logic [7:0] result
);

  // Functional correctness (sample after combinational settle via ##0)
  property add_ok;
    @(num1 or num2 or op or result)
      (op==2'b00) |-> ##0 (result == (num1 + num2));
  endproperty
  assert property (add_ok);

  property sub_ok;
    @(num1 or num2 or op or result)
      (op==2'b01) |-> ##0 (result == (num1 - num2));
  endproperty
  assert property (sub_ok);

  property mul_ok;
    @(num1 or num2 or op or result)
      (op==2'b10) |-> ##0 (result == (num1 * num2)[7:0]);
  endproperty
  assert property (mul_ok);

  property div_ok;
    @(num1 or num2 or op or result)
      (op==2'b11 && (num2!=0)) |-> ##0 (result == (num1 / num2));
  endproperty
  assert property (div_ok);

  // Division-by-zero must drive Xs
  property div_by_zero_x;
    @(num1 or num2 or op or result)
      (op==2'b11 && (num2==0)) |-> ##0 $isunknown(result);
  endproperty
  assert property (div_by_zero_x);

  // No X/Z on result except for divide-by-zero case
  property no_x_when_safe;
    @(num1 or num2 or op or result)
      !(op==2'b11 && num2==0) |-> ##0 !$isunknown(result);
  endproperty
  assert property (no_x_when_safe);

  // Basic functional coverage: exercise each opcode
  cover property (@(num1 or num2 or op)) (op==2'b00);
  cover property (@(num1 or num2 or op)) (op==2'b01);
  cover property (@(num1 or num2 or op)) (op==2'b10);
  cover property (@(num1 or num2 or op)) (op==2'b11);

  // Corner-case coverage
  // Add overflow (carry-out)
  cover property (@(num1 or num2 or op))
    (op==2'b00 && ({1'b0,num1}+{1'b0,num2})[8]);

  // Sub underflow (borrow)
  cover property (@(num1 or num2 or op))
    (op==2'b01 && (num1 < num2));

  // Mul overflow (upper 8 bits non-zero)
  cover property (@(num1 or num2 or op))
    (op==2'b10 && ((num1*num2)[15:8] != 8'h00));

  // Div with remainder
  cover property (@(num1 or num2 or op))
    (op==2'b11 && num2!=0 && (num1 % num2)!=0);

  // Div by zero event
  cover property (@(num1 or num2 or op))
    (op==2'b11 && num2==0);

endmodule

// Bind into DUT (instantiate once in your environment)
// bind calculator calculator_sva u_calculator_sva (.*);