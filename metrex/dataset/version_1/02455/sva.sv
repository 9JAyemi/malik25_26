// SVA checker for control. Bind this to the DUT; provide any free-running clk.
// Example bind:
// bind control control_sva u_control_sva (.clk(tb_clk), .op(op), .alu_op(alu_op),
//   .regDst(regDst), .aluSrc(aluSrc), .memToReg(memToReg), .regWrite(regWrite),
//   .memRead(memRead), .memWrite(memWrite), .branch(branch));

module control_sva (
  input  logic        clk,
  input  logic [5:0]  op,
  input  logic [1:0]  alu_op,
  input  logic        regDst, aluSrc, memToReg, regWrite,
  input  logic        memRead, memWrite, branch
);
  logic [5:0] opb; assign opb = ~op;

  default clocking cb @(posedge clk); endclocking

  // No X/Z on any output
  a_no_x: assert property (!$isunknown({alu_op,regDst,aluSrc,memToReg,regWrite,memRead,memWrite,branch})));

  // Combinational consistency (outputs equal their Boolean functions of op)
  a_aluop0:  assert property (alu_op[0] == (opb[0] & opb[1] & opb[2] & op[2] & opb[4] & opb[5]));
  a_aluop1:  assert property (alu_op[1] == (&opb)); // op==6'b0
  a_regDst:  assert property (regDst     == (&opb));
  a_mem2reg: assert property (memToReg   == (op[0] & opb[1] & opb[2] & opb[3] & op[4] & op[5]));
  a_regWr:   assert property (regWrite   == ((op[0] & opb[1] & opb[2] & opb[3] & opb[4] & opb[5]) |
                                             (op[5] & opb[1] & opb[2] & opb[3] & opb[4] & opb[5])));
  a_memRd:   assert property (memRead    == (op[0] & opb[1] & opb[2] & opb[3] & op[4] & opb[5]));
  a_memWr:   assert property (memWrite   == (op[0] & opb[1]             & opb[3] & opb[4] & opb[5]));
  a_branch:  assert property (branch     == (opb[0] & opb[1] & opb[2] & op[2] & opb[4] & opb[5]));
  a_aluSrc:  assert property (aluSrc     == (op[5] & opb[1] & opb[2] & op[4] & op[3]));

  // Derived relationships from the DUT equations
  a_rel1:    assert property (alu_op[1] == regDst);
  a_rel2:    assert property (alu_op[0] == branch);
  a_rw_excl: assert property (!(memRead && memWrite));

  // Combinational stability: if op is stable, outputs remain stable
  a_stable:  assert property ($stable(op) |-> $stable({alu_op,regDst,aluSrc,memToReg,regWrite,memRead,memWrite,branch}));

  // Functional coverage (hit each control high at least once; also key op patterns)
  c_aluop1:    cover property (alu_op[1]);
  c_regDst:    cover property (regDst);
  c_mem2reg:   cover property (memToReg);
  c_regWrite:  cover property (regWrite);
  c_memRead:   cover property (memRead);
  c_memWrite:  cover property (memWrite);
  c_branch:    cover property (branch);
  c_aluSrc:    cover property (aluSrc);
  c_aluop0:    cover property (alu_op[0]);

  // Specific opcode minterms seen in DUT equations
  c_Rtype:     cover property ((&opb) && regDst && alu_op[1]);                  // op==6'b000000
  c_regWr_m0:  cover property ((op==6'b000001) && regWrite);                    // first regWrite minterm
  c_regWr_m1:  cover property ((op[5] && (op[4:0]==5'b00000)) && regWrite);     // second regWrite minterm (unreachable per DUT)
  c_memRd_op:  cover property ((op[5:0]==6'b010001) && memRead);                // memRead minterm
  c_mem2reg_op:cover property ((op[5:0]==6'b110001) && memToReg);               // memToReg minterm
endmodule