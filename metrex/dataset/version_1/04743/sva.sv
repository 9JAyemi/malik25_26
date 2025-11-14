// SVA checker for simple_calculator (bind this to the DUT)
module simple_calculator_sva;

  // Full-precision helpers
  wire [8:0]  add9  = {1'b0, operand_a} + {1'b0, operand_b};
  wire [8:0]  sub9  = {1'b0, operand_a} - {1'b0, operand_b};
  wire [15:0] mul16 = operand_a * operand_b;

  // Combinational sampling event
  event comb_ev;
  always @(operation or operand_a or operand_b or result or overflow or underflow) -> comb_ev;

  // Valid opcode only
  ap_valid_op: assert property (@(comb_ev) operation inside {3'b000,3'b001,3'b010,3'b011});

  // Outputs known for valid cases (and nonzero divisor)
  ap_known: assert property (@(comb_ev)
    (operation inside {3'b000,3'b001,3'b010} || (operation==3'b011 && operand_b!=0))
    |-> ##0 !$isunknown({result,overflow,underflow}));

  // Flags cannot both be 1
  ap_flags_mutex: assert property (@(comb_ev) ##0 !(overflow && underflow));

  // Addition
  ap_add_res: assert property (@(comb_ev)
    (operation==3'b000) |-> ##0 (result==add9[7:0] && overflow==add9[8] && underflow==1'b0));

  // Subtraction
  ap_sub_res: assert property (@(comb_ev)
    (operation==3'b001) |-> ##0 (result==sub9[7:0] && underflow==sub9[8] && overflow==1'b0));

  // Multiplication
  ap_mul_res: assert property (@(comb_ev)
    (operation==3'b010) |-> ##0 (result==mul16[7:0] && overflow==(|mul16[15:8]) && underflow==1'b0));

  // Division: forbid divide-by-zero
  ap_div_no_zero: assert property (@(comb_ev) (operation==3'b011) |-> ##0 (operand_b!=0));

  // Division (valid)
  ap_div_res: assert property (@(comb_ev)
    (operation==3'b011 && operand_b!=0) |-> ##0 (result==(operand_a/operand_b) && overflow==1'b0 && underflow==1'b0));

  // Overflow only allowed for add/mul
  ap_overflow_ops: assert property (@(comb_ev)
    (operation inside {3'b001,3'b011}) |-> ##0 (overflow==1'b0));

  // Coverage
  cp_add:       cover property (@(comb_ev) (operation==3'b000));
  cp_add_ovf:   cover property (@(comb_ev) (operation==3'b000 && add9[8]));
  cp_sub:       cover property (@(comb_ev) (operation==3'b001));
  cp_sub_udf:   cover property (@(comb_ev) (operation==3'b001 && sub9[8]));
  cp_mul:       cover property (@(comb_ev) (operation==3'b010));
  cp_mul_ovf:   cover property (@(comb_ev) (operation==3'b010 && |mul16[15:8]));
  cp_div:       cover property (@(comb_ev) (operation==3'b011 && operand_b!=0));

endmodule

// Bind into the DUT
bind simple_calculator simple_calculator_sva sva_inst();