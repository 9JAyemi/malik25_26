// SVA checker for calculator
module calculator_sva
(
  input  logic [7:0]  operand1,
  input  logic [7:0]  operand2,
  input  logic [1:0]  operator,
  input  logic [15:0] result
);
  default clocking cb @(posedge $global_clock); endclocking

  // Sanity/knownness
  ap_inputs_known:    assert property (!$isunknown({operand1,operand2,operator}));
  ap_no_x_out_valid:  assert property (( !$isunknown({operand1,operand2,operator})
                                        && !(operator==2'b11 && operand2==8'd0))
                                       |-> !$isunknown(result));

  // Functional correctness
  ap_add: assert property (operator==2'b00 |-> result == (operand1 + operand2));
  ap_sub: assert property (operator==2'b01 |-> result == (operand1 - operand2));
  ap_mul: assert property (operator==2'b10 |-> result == (operand1 * operand2));
  ap_div_guard: assert property (operator==2'b11 |-> (operand2!=8'd0) or $isunknown(result));
  ap_div: assert property ((operator==2'b11 && operand2!=8'd0) |-> result == (operand1 / operand2));

  // Combinational stability
  ap_stable: assert property ($stable({operand1,operand2,operator}) |-> $stable(result));

  // Coverage
  cp_op_add: cover property (operator==2'b00);
  cp_op_sub: cover property (operator==2'b01);
  cp_op_mul: cover property (operator==2'b10);
  cp_op_div: cover property (operator==2'b11);
  cp_add_max:        cover property (operator==2'b00 && operand1==8'hFF && operand2==8'hFF && result==16'd510);
  cp_sub_underflow:  cover property (operator==2'b01 && operand1==8'h00 && operand2==8'hFF && result==16'h01FF);
  cp_mul_zero:       cover property (operator==2'b10 && (operand1==8'd0 || operand2==8'd0) && result==16'd0);
  cp_mul_max:        cover property (operator==2'b10 && operand1==8'hFF && operand2==8'hFF && result==16'd65025);
  cp_div_by_zero:    cover property (operator==2'b11 && operand2==8'd0);
  cp_div_by_one:     cover property (operator==2'b11 && operand2==8'd1 && result==operand1);
  cp_div_equal:      cover property (operator==2'b11 && operand1==8'hFF && operand2==8'hFF && result==16'd1);
endmodule

// Bind into DUT
bind calculator calculator_sva sva_i (.*);