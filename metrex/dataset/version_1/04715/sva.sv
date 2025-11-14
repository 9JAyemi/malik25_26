// SVA for calculator: checks reset, latency, hold behavior, correctness, and basic coverage

module calculator_sva (
  input logic        clk, reset,
  input logic [1:0]  operation,
  input logic [7:0]  operand1, operand2,
  input logic [7:0]  result,
  input logic [7:0]  temp_result
);

  // Default clocking for concise assertions
  default clocking cb @(posedge clk); endclocking

  // X/Z checks
  assert property (@cb !$isunknown({reset,operation,operand1,operand2}));
  assert property (@cb !$isunknown({result,temp_result}));

  // Synchronous reset clears regs
  assert property (@cb reset |-> (result==8'h00 && temp_result==8'h00));

  // Hold when operation is invalid (10/11)
  assert property (@cb disable iff (reset)
                   (operation inside {2'b10,2'b11}) |-> (temp_result==$past(temp_result) && result==$past(result)));

  // temp_result updates 1-cycle after valid op using current operands
  assert property (@cb disable iff (reset) (operation==2'b00) |=> temp_result == (operand1 + operand2));
  assert property (@cb disable iff (reset) (operation==2'b01) |=> temp_result == (operand1 - operand2));

  // result updates in the same cycle of a valid op from previous temp_result
  assert property (@cb disable iff (reset) (operation inside {2'b00,2'b01}) |-> result == $past(temp_result));

  // Coverage: exercise ops, invalid op, and back-to-back ops
  cover property (@cb disable iff (reset) (operation==2'b00));
  cover property (@cb disable iff (reset) (operation==2'b01));
  cover property (@cb disable iff (reset) (operation inside {2'b10,2'b11}));
  cover property (@cb disable iff (reset) (operation==2'b00) ##1 (operation==2'b01));
  cover property (@cb disable iff (reset) (operation==2'b01) ##1 (operation==2'b00));

endmodule

// Bind into DUT (includes internal temp_result)
bind calculator calculator_sva i_calculator_sva(.*);