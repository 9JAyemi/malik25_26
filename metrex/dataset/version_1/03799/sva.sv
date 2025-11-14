// SVA for Floating_Point_Arithmetic
// Bind to the DUT; provide a clock from your TB/environment.
module Floating_Point_Arithmetic_sva (
  input logic               clk,
  input logic [31:0]        operand1,
  input logic [31:0]        operand2,
  input logic [1:0]         operation,
  input logic [31:0]        result,
  // internal DUT regs (reachable via bind)
  input logic [31:0]        add_result,
  input logic [31:0]        sub_result,
  input logic [31:0]        mul_result,
  input logic [31:0]        div_result,
  input logic [31:0]        operand2_neg
);

  default clocking cb @(posedge clk); endclocking

  // Combinational function checks
  // Note: guard unknowns to avoid X-driven false fails; explicitly check div-by-0 behavior.
  assert property ( !$isunknown({operand1,operand2}) |-> add_result == operand1 + operand2 )
    else $error("add_result mismatch");

  assert property ( !$isunknown({operand1,operand2,operand2_neg}) |-> sub_result == operand1 - operand2_neg )
    else $error("sub_result mismatch");

  assert property ( !$isunknown({operand1,operand2}) |-> mul_result == operand1 * operand2 )
    else $error("mul_result mismatch");

  assert property ( !$isunknown({operand1,operand2}) && (operand2!=32'd0) |-> div_result == operand1 / operand2 )
    else $error("div_result mismatch (non-zero divisor)");

  assert property ( (operand2==32'd0) |-> $isunknown(div_result) )
    else $error("div_result should be X on divide-by-zero");

  // Negation correctness (bug catcher): two's complement should be ~operand2 + 1
  assert property ( !$isunknown(operand2) |-> operand2_neg == (~operand2 + 32'd1) )
    else $error("operand2_neg is not a true two's-complement negate");

  // Result select/mux correctness
  assert property (
    !$isunknown(operation) |->
      (operation==2'b00 && result==add_result) ||
      (operation==2'b01 && result==sub_result) ||
      (operation==2'b10 && result==mul_result) ||
      (operation==2'b11 && result==div_result)
  ) else $error("result not selected from correct arithmetic path");

  // Direct functional check of result for known inputs
  assert property (
    !$isunknown({operand1,operand2,operation}) |->
      (operation==2'b00 && result==operand1 + operand2) ||
      (operation==2'b01 && result==operand1 - operand2_neg) ||
      (operation==2'b10 && result==operand1 * operand2) ||
      (operation==2'b11 && (operand2!=32'd0) && result==operand1 / operand2) ||
      (operation==2'b11 && (operand2==32'd0) && $isunknown(result))
  ) else $error("result functional mismatch");

  // Default branch on unknown operation encodings should force 0
  assert property ( $isunknown(operation) |-> result == 32'h0 )
    else $error("default case (unknown operation) should drive result==0");

  // No-X guarantee when inputs are known and divide-by-zero not selected
  assert property (
    !$isunknown({operand1,operand2,operation}) && !(operation==2'b11 && operand2==32'd0) |-> !$isunknown(result)
  ) else $error("Unexpected X/Z in result with known inputs");

  // Coverage
  cover property ( !$isunknown(operation) && operation==2'b00 );
  cover property ( !$isunknown(operation) && operation==2'b01 );
  cover property ( !$isunknown(operation) && operation==2'b10 );
  cover property ( !$isunknown(operation) && operation==2'b11 );
  cover property ( operation==2'b11 && operand2==32'd0 );                // div-by-zero scenario
  cover property ( $isunknown(operation) && result==32'h0 );             // default case used
  cover property ( operand2[31] && (operand2_neg != (~operand2 + 32'd1)) ); // highlight negation bug

endmodule

// Example bind (place in TB or a package included by TB)
// bind Floating_Point_Arithmetic Floating_Point_Arithmetic_sva sva (
//   .clk        (clk),
//   .operand1   (operand1),
//   .operand2   (operand2),
//   .operation  (operation),
//   .result     (result),
//   .add_result (add_result),
//   .sub_result (sub_result),
//   .mul_result (mul_result),
//   .div_result (div_result),
//   .operand2_neg(operand2_neg)
// );