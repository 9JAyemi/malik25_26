// SVA for calculator
// Bindable, concise, checks arithmetic semantics and key corner cases

module calculator_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [1:0]  op,
  input  logic [7:0]  operand1,
  input  logic [7:0]  operand2,
  input  logic [7:0]  result,
  input  logic        overflow
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset drives outputs to 0 on next cycle
  a_reset_clears: assert property (@(posedge clk) reset |=> (result==8'd0 && overflow==1'b0));

  // Inputs and outputs must not be X/Z (outside reset)
  a_inputs_known:  assert property (!$isunknown({op, operand1, operand2}));
  a_outputs_known: assert property (!$isunknown({result, overflow}));

  // Addition: unsigned 9-bit sum = {carry, sum[7:0]}
  a_add: assert property (
    op==2'b00 |=> {overflow, result} == ({1'b0,operand1} + {1'b0,operand2})
  );

  // Subtraction: 8-bit result wraps; overflow = signed overflow
  a_sub_result: assert property (
    op==2'b01 |=> result == (operand1 - operand2)
  );
  a_sub_overflow_signed: assert property (
    op==2'b01 |=> overflow == ((operand1[7]^operand2[7]) & ((operand1 - operand2)[7] ^ operand1[7]))
  );

  // Multiplication: result = low 8 bits; overflow if any upper bits set
  a_mul: assert property (
    op==2'b10 |=> (result == (operand1*operand2)[7:0]) && (overflow == |( (operand1*operand2)[15:8] ))
  );

  // Division: by zero -> result 0, overflow 1; else normal quotient, overflow 0
  a_div_by_zero: assert property (
    (op==2'b11 && operand2==8'd0) |=> (result==8'd0 && overflow==1'b1)
  );
  a_div_normal: assert property (
    (op==2'b11 && operand2!=8'd0) |=> (result == (operand1/operand2) && overflow==1'b0)
  );

  // Optional sanity: op should be 2-state to avoid hitting default branch via X/Z
  a_op_2state: assert property (!$isunknown(op));

  // Functional coverage (key scenarios)
  c_add_overflow:     cover property (op==2'b00 |=> overflow);
  c_add_no_overflow:  cover property (op==2'b00 |=> !overflow);
  c_sub_overflow:     cover property (op==2'b01 |=> overflow);
  c_sub_no_overflow:  cover property (op==2'b01 |=> !overflow);
  c_mul_overflow:     cover property (op==2'b10 |=> overflow);
  c_mul_no_overflow:  cover property (op==2'b10 |=> !overflow);
  c_div_by_zero:      cover property (op==2'b11 && operand2==0 |=> overflow);
  c_div_normal:       cover property (op==2'b11 && operand2!=0 |=> !overflow);

endmodule

// Bind into DUT
bind calculator calculator_sva calculator_sva_i (.*);