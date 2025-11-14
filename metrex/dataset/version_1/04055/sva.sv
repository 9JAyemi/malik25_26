// SVA for simple_calculator
// Uses $global_clock to sample combinational behavior.

module simple_calculator_sva(
  input logic [7:0] A,
  input logic [7:0] B,
  input logic [1:0] opcode,
  input logic [7:0] result
);
  default clocking cb @($global_clock); endclocking

  // Helpful expressions
  let sum9   = {1'b0,A} + {1'b0,B};
  let diff9  = {1'b0,A} - {1'b0,B};
  let prod16 = A * B;

  // Sanity: inputs should be known (avoid latch from X opcode)
  a_no_x_inputs: assert property (!$isunknown({A,B,opcode}))
    else $error("simple_calculator: X/Z on inputs");

  // Functional correctness per opcode (same-cycle, guarded by known inputs)
  a_add: assert property ( (!$isunknown({A,B,opcode})) && opcode==2'b00 |-> ##0 result == (A + B)[7:0] )
    else $error("ADD mismatch");

  a_sub: assert property ( (!$isunknown({A,B,opcode})) && opcode==2'b01 |-> ##0 result == (A - B)[7:0] )
    else $error("SUB mismatch");

  a_mul: assert property ( (!$isunknown({A,B,opcode})) && opcode==2'b10 |-> ##0 result == (A * B)[7:0] )
    else $error("MUL mismatch");

  a_div_nz: assert property ( (!$isunknown({A,B,opcode})) && opcode==2'b11 && (B!=8'h00) |-> ##0 result == (A / B) )
    else $error("DIV mismatch (B!=0)");

  // Divide-by-zero should yield X on result in simulation
  a_div_zero_x: assert property ( (!$isunknown({A,B,opcode})) && opcode==2'b11 && (B==8'h00) |-> ##0 $isunknown(result) )
    else $error("DIV by zero should produce X result");

  // Result should not change if inputs/opcode do not change
  a_stable_when_inputs_stable: assert property ( $stable({A,B,opcode}) |-> ##0 $stable(result) )
    else $error("Result changed while inputs/opcode stable");

  // Functional coverage
  c_op_add: cover property (opcode==2'b00);
  c_op_sub: cover property (opcode==2'b01);
  c_op_mul: cover property (opcode==2'b10);
  c_op_div: cover property (opcode==2'b11);

  // Corner/overflow/edge scenarios
  c_add_overflow:   cover property (opcode==2'b00 && sum9[8]==1'b1);
  c_sub_borrow:     cover property (opcode==2'b01 && A < B);
  c_mul_overflow:   cover property (opcode==2'b10 && prod16[15:8] != 8'h00);
  c_div_by_zero:    cover property (opcode==2'b11 && B==8'h00);
  c_div_q_zero:     cover property (opcode==2'b11 && B!=8'h00 && A < B);
  c_add_zero_op:    cover property (opcode==2'b00 && (A==8'h00 || B==8'h00));
  c_sub_equal:      cover property (opcode==2'b01 && A==B);
  c_mul_zero:       cover property (opcode==2'b10 && (A==8'h00 || B==8'h00));
  c_div_by_one:     cover property (opcode==2'b11 && B==8'h01);

endmodule

// Bind into the DUT
bind simple_calculator simple_calculator_sva u_simple_calculator_sva (.*);