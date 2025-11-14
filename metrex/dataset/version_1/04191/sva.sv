// SVA for arithmetic_op
module arithmetic_op_sva (
  input  logic        clk,
  input  logic [7:0]  result,
  input  logic [7:0]  operand1,
  input  logic [7:0]  operand2,
  input  logic [1:0]  select
);

  // Basic sanity: inputs and output must be known (no X/Z)
  a_inputs_known: assert property (@(posedge clk) !$isunknown({select, operand1, operand2}));
  a_result_known: assert property (@(posedge clk) !$isunknown(result));

  // Functional correctness (registered, 1-cycle latency)
  a_add: assert property (@(posedge clk) ($past(select) == 2'b00) |-> result == ($past(operand1) + $past(operand2)));
  a_sub: assert property (@(posedge clk) ($past(select) == 2'b01) |-> result == ($past(operand1) - $past(operand2)));
  a_and: assert property (@(posedge clk) ($past(select) == 2'b10) |-> result == ($past(operand1) & $past(operand2)));
  a_or : assert property (@(posedge clk) ($past(select) == 2'b11) |-> result == ($past(operand1) | $past(operand2)));

  // Stability: if inputs/select are stable across a cycle, result must hold
  a_hold_when_inputs_stable: assert property (@(posedge clk)
    $stable({select, operand1, operand2}) |-> result == $past(result)
  );

  // Functional coverage
  c_add_req: cover property (@(posedge clk) select == 2'b00);
  c_sub_req: cover property (@(posedge clk) select == 2'b01);
  c_and_req: cover property (@(posedge clk) select == 2'b10);
  c_or_req : cover property (@(posedge clk) select == 2'b11);

  // Interesting corner cases
  c_add_overflow : cover property (@(posedge clk) ($past(select)==2'b00) && (result < $past(operand1)));
  c_sub_underflow: cover property (@(posedge clk) ($past(select)==2'b01) && (result > $past(operand1)));
  c_and_zero     : cover property (@(posedge clk) ($past(select)==2'b10) && (result == 8'h00));
  c_or_allones   : cover property (@(posedge clk) ($past(select)==2'b11) && (result == 8'hFF));

endmodule

// Bind to DUT
bind arithmetic_op arithmetic_op_sva sva_inst (
  .clk     (clk),
  .result  (result),
  .operand1(operand1),
  .operand2(operand2),
  .select  (select)
);