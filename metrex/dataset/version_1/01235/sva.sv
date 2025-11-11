// SVA for logic_operation. Bind this checker to the DUT.
// Example bind:
// bind logic_operation logic_operation_sva u_logic_operation_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));

module logic_operation_sva (
  input logic               clk,
  input logic               rst_n,
  input logic [1:0]         logic_op_x,
  input logic [31:0]        operand_0_x,
  input logic [31:0]        operand_1_x,
  input logic [31:0]        logic_result_x
);

default clocking cb @(posedge clk); endclocking

// Purely combinational behavior: if inputs stable, output stable
assert property (disable iff(!rst_n)
  $stable({logic_op_x,operand_0_x,operand_1_x}) |-> $stable(logic_result_x))
  else $error("logic_result_x changed while inputs stable");

// Functional correctness per opcode
assert property (disable iff(!rst_n)
  (logic_op_x==2'b00) |-> (logic_result_x == (operand_0_x & operand_1_x)))
  else $error("AND mismatch");

assert property (disable iff(!rst_n)
  (logic_op_x==2'b01) |-> (logic_result_x == (operand_0_x | operand_1_x)))
  else $error("OR mismatch");

assert property (disable iff(!rst_n)
  (logic_op_x==2'b10) |-> (logic_result_x == (operand_0_x ^ operand_1_x)))
  else $error("XOR mismatch");

assert property (disable iff(!rst_n)
  (logic_op_x==2'b11) |-> (logic_result_x == 32'h0))
  else $error("DEFAULT mismatch");

// Known-in => known-out
assert property (disable iff(!rst_n)
  !$isunknown({logic_op_x,operand_0_x,operand_1_x}) |-> !$isunknown(logic_result_x))
  else $error("Unknown output with known inputs");

// With X/Z opcode, case default should drive zero
assert property (disable iff(!rst_n)
  $isunknown(logic_op_x) |-> (logic_result_x == 32'h0))
  else $error("Default on X/Z opcode not zero");

// Opcode coverage
cover property (logic_op_x==2'b00);
cover property (logic_op_x==2'b01);
cover property (logic_op_x==2'b10);
cover property (logic_op_x==2'b11);

// Data-pattern coverage
cover property ((logic_op_x==2'b10) && (operand_0_x==operand_1_x) && (logic_result_x==32'h0));              // XOR equal -> 0
cover property ((logic_op_x==2'b10) && (operand_0_x==~operand_1_x) && (logic_result_x==32'hFFFF_FFFF));      // XOR comp -> all 1s
cover property ((logic_op_x==2'b00) && ((operand_0_x==32'h0)||(operand_1_x==32'h0)) && (logic_result_x==32'h0));
cover property ((logic_op_x==2'b01) && (operand_0_x==32'h0) && (operand_1_x==32'h0) && (logic_result_x==32'h0));
cover property ((logic_op_x==2'b00) && (operand_0_x==32'hFFFF_FFFF) && (operand_1_x==32'hFFFF_FFFF) && (logic_result_x==32'hFFFF_FFFF));
cover property ((logic_op_x==2'b01) && ((operand_0_x|operand_1_x)==32'hFFFF_FFFF) && (logic_result_x==32'hFFFF_FFFF));

endmodule