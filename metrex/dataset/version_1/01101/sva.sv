// SVA checker for 'control' (combinational). Bind this file to the DUT.
`ifndef CONTROL_SVA_SV
`define CONTROL_SVA_SV

module control_sva (
  input  logic [5:0] op,
  input  logic [1:0] alu_op,
  input  logic       regDst, aluSrc, memToReg, regWrite,
  input  logic       memRead, memWrite, branch
);

  localparam logic [5:0] OP_RTYPE = 6'b000000;
  localparam logic [5:0] OP_BEQ   = 6'b000100;
  localparam logic [5:0] OP_LW    = 6'b100011;
  localparam logic [5:0] OP_SW    = 6'b101011;

  // No X/Z on outputs when inputs are known
  assert property (@(*) !$isunknown(op) |-> !$isunknown({alu_op,regDst,aluSrc,memToReg,regWrite,memRead,memWrite,branch}));

  // Exact boolean equivalence to gate-level decode
  assert property (@(*) alu_op[1] == (&~op));
  assert property (@(*) alu_op[0] == (~op[5] & ~op[4] & ~op[3] &  op[2] & ~op[1] & ~op[0]));
  assert property (@(*) regDst    == (&~op));
  assert property (@(*) memToReg  == ( op[5] & ~op[4] & ~op[3] & ~op[2] &  op[1] &  op[0]));
  assert property (@(*) memRead   == ( op[5] & ~op[4] & ~op[3] & ~op[2] &  op[1] &  op[0]));
  assert property (@(*) memWrite  == ( op[5] & ~op[4] &  op[3] & ~op[2] &  op[1] &  op[0]));
  assert property (@(*) branch    == (~op[5] & ~op[4] & ~op[3] &  op[2] & ~op[1] & ~op[0]));
  assert property (@(*) aluSrc    == ( op[5] & ~op[4] & ~op[2] &  op[1] &  op[0]));

  // Structural invariants
  assert property (@(*) regDst == alu_op[1]);
  assert property (@(*) memToReg == memRead);
  assert property (@(*) regWrite == (memRead || alu_op[1]));
  assert property (@(*) aluSrc == (memRead || memWrite));
  assert property (@(*) !(memRead && memWrite));
  assert property (@(*) !(alu_op[1] && alu_op[0]));

  // Outputs imply opcode (one-hot decode checks)
  assert property (@(*) memRead   |-> op == OP_LW);
  assert property (@(*) memWrite  |-> op == OP_SW);
  assert property (@(*) branch    |-> op == OP_BEQ);
  assert property (@(*) regDst    |-> op == OP_RTYPE);
  assert property (@(*) alu_op[1] |-> op == OP_RTYPE);
  assert property (@(*) alu_op[0] |-> op == OP_BEQ);

  // Per-opcode truth table
  assert property (@(*) (op == OP_RTYPE) |->
                   (alu_op==2'b10 && regDst && !aluSrc && !memToReg && regWrite && !memRead && !memWrite && !branch));
  assert property (@(*) (op == OP_LW)    |->
                   (alu_op==2'b00 && !regDst &&  aluSrc &&  memToReg && regWrite &&  memRead && !memWrite && !branch));
  assert property (@(*) (op == OP_SW)    |->
                   (alu_op==2'b00 && !regDst &&  aluSrc && !memToReg && !regWrite && !memRead &&  memWrite && !branch));
  assert property (@(*) (op == OP_BEQ)   |->
                   (alu_op==2'b01 && !regDst && !aluSrc && !memToReg && !regWrite && !memRead && !memWrite &&  branch));

  // All other opcodes drive all zeros
  assert property (@(*) (!(op inside {OP_RTYPE,OP_LW,OP_SW,OP_BEQ})) |->
                   (alu_op==2'b00 && !regDst && !aluSrc && !memToReg && !regWrite && !memRead && !memWrite && !branch));

  // Coverage: hit each decode and both memRead/memWrite cases
  cover property (@(*) op == OP_RTYPE);
  cover property (@(*) op == OP_LW);
  cover property (@(*) op == OP_SW);
  cover property (@(*) op == OP_BEQ);
  cover property (@(*) memRead && !memWrite);
  cover property (@(*) memWrite && !memRead);

endmodule

bind control control_sva control_sva_i (.*);

`endif