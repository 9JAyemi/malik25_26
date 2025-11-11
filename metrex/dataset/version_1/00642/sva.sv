// SVA for CONTROL_UNIT — concise, full functional checks and key coverage
// Bind this file to the DUT without modifying it.

module CONTROL_UNIT_SVA (
  input  logic [5:0] op,
  input  logic [5:0] func,
  input  logic       z,
  input  logic       wreg,
  input  logic       regrt,
  input  logic       jal,
  input  logic       m2reg,
  input  logic       shfit,
  input  logic       aluimm,
  input  logic       sext,
  input  logic       wmem,
  input  logic [3:0] aluc,
  input  logic [1:0] pcsource
);
  default clocking cb @(*) endclocking

  // Combinational equivalence to DUT logic
  assert property (wreg   == (~op[5] | (op == 6'b100011)));
  assert property (regrt  == ( op[5] & ~op[2]));
  assert property (jal    == (op == 6'b000011));
  assert property (m2reg  == (op == 6'b100011));
  assert property (shfit  == ((func == 6'b000000) & ~op[5]));
  assert property (aluimm == ( op[5] & ~op[3]));
  assert property (sext   == ~(op[5] &  op[3]));
  assert property (wmem   == (op == 6'b101011));

  assert property (aluc[3] == ((func == 6'b000011) & ~op[5]));
  assert property (aluc[2] == (((op == 6'b000100) &  z) | ((op == 6'b000101) & ~z)));
  assert property (aluc[1:0] == ((op[5:3] == 3'b000) ? func[1:0] : op[1:0]));

  assert property (pcsource[1] == ((op == 6'b000010) | (op == 6'b000011)));
  assert property (pcsource[0] == (((op == 6'b000100) &  z) | ((op == 6'b000101) & ~z)));

  // Cross-checks/relations implied by the DUT encodings
  assert property (pcsource[0] == aluc[2]);               // identical expression in DUT
  assert property (wmem |-> !wreg);                       // sw never writes register per DUT equations
  assert property (m2reg |-> (wreg && regrt && !wmem));   // lw implies these per DUT equations
  assert property (jal   |-> (wreg && !m2reg && !wmem && pcsource == 2'b10));

  // X-propagation guard: if inputs are known, outputs must be known
  assert property (!$isunknown({op,func,z}) |-> !$isunknown({wreg,regrt,jal,m2reg,shfit,aluimm,sext,wmem,aluc,pcsource}));

  // Key functional coverage (instruction classes and control patterns)
  cover property (op == 6'b100011 && m2reg && wreg && regrt && !wmem && pcsource == 2'b00); // lw
  cover property (op == 6'b101011 && wmem && !wreg);                                        // sw
  cover property (op == 6'b000100 &&  z && pcsource[0] && aluc[2]);                          // beq taken
  cover property (op == 6'b000101 && !z && pcsource[0] && aluc[2]);                          // bne taken
  cover property (op == 6'b000010 && pcsource == 2'b10 && !jal);                             // j
  cover property (op == 6'b000011 && jal && wreg && pcsource == 2'b10);                      // jal
  cover property ((op[5:3] == 3'b000) && (func == 6'b000000) && shfit);                      // sll-style shift
  cover property ((op[5:3] == 3'b000) && (func == 6'b000011) && aluc[3]);                    // sra
  cover property ( op[5] && !op[3] && aluimm && !m2reg && !wmem);                            // I-type ALU per DUT logic
  cover property (!(op[5] & op[3]) && sext);                                                 // sign-extend = 1
  cover property ( (op[5] & op[3]) && !sext);                                                // sign-extend = 0 (e.g., DUT's "lui"-like case)

endmodule

bind CONTROL_UNIT CONTROL_UNIT_SVA control_unit_sva_i (
  .op(op),
  .func(func),
  .z(z),
  .wreg(wreg),
  .regrt(regrt),
  .jal(jal),
  .m2reg(m2reg),
  .shfit(shfit),
  .aluimm(aluimm),
  .sext(sext),
  .wmem(wmem),
  .aluc(aluc),
  .pcsource(pcsource)
);