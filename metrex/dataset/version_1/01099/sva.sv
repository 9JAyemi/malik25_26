// SVA checker for calculator
module calculator_sva (
  input logic [7:0] result,
  input logic [7:0] num1,
  input logic [7:0] num2,
  input logic [2:0] op
);

  // Sample on any input change; ignore X/Z on inputs
  default clocking cb @(num1 or num2 or op); endclocking
  default disable iff ($isunknown({num1,num2,op}));

  // Functional correctness (allow a delta for combinational settle)
  assert_add: assert property (op==3'b000 |-> ##0 result == (num1 + num2));
  assert_sub: assert property (op==3'b001 |-> ##0 result == (num1 - num2));
  assert_mul: assert property (op==3'b010 |-> ##0 result == (num1 * num2)[7:0]);
  assert_div: assert property ((op==3'b011) && (num2!=0) |-> ##0 result == (num1 / num2));
  assert_no_div0: assert property (!(op==3'b011 && num2==0));
  assert_default_zero: assert property (op[2] |-> ##0 result == 8'h00);

  // Result must be known for all defined operations (excluding div-by-zero)
  assert_known_result: assert property (
    (op inside {3'b000,3'b001,3'b010,3'b011}) && !(op==3'b011 && num2==0)
    |-> ##0 !$isunknown(result)
  );

  // Coverage
  cover_add:          cover property (op==3'b000);
  cover_sub:          cover property (op==3'b001);
  cover_mul:          cover property (op==3'b010);
  cover_div:          cover property (op==3'b011);
  cover_default:      cover property (op[2]);

  // Corner-case coverage
  cover_add_carry:    cover property (op==3'b000 && ({1'b0,num1}+{1'b0,num2})[8]);
  cover_sub_borrow:   cover property (op==3'b001 && (num1 < num2));
  cover_mul_overflow: cover property (op==3'b010 && ((num1 * num2)[15:8] != 8'h00));
  cover_div_valid:    cover property (op==3'b011 && num2!=0);
  cover_div_by_zero:  cover property (op==3'b011 && num2==0);

endmodule

// Bind into DUT
bind calculator calculator_sva u_calculator_sva (
  .result(result),
  .num1(num1),
  .num2(num2),
  .op(op)
);