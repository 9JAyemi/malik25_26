// SVA checker for control_unit
// Bind this module to your DUT instance: 
//   bind control_unit control_unit_sva u_control_unit_sva(.*);

module control_unit_sva(
  input  wire [5:0] op, func,
  input  wire [4:0] rs, rt, mrn, ern,
  input  wire       mm2reg, mwreg, em2reg, ewreg, rsrtequ,
  input  wire       wpcir, wreg, m2reg, wmem, jal, aluimm, shift, regrt, sext,
  input  wire [3:0] daluc,
  input  wire [1:0] pcsource, fwda, fwdb
);

  // recompute golden decodes and outputs
  logic r;
  logic i_and,i_or,i_xor,i_add,i_sub,i_addi,i_andi,i_ori,i_xori,i_lw,i_sw,i_beq,i_bne,i_sll,i_srl,i_sra,i_jr,i_j,i_jal,i_lui,i_rs,i_rt;
  logic [3:0] exp_daluc;
  logic       exp_wpcir, exp_wreg, exp_wmem, exp_m2reg, exp_jal, exp_aluimm, exp_shift, exp_regrt, exp_sext;
  logic [1:0] exp_pcsource, exp_fwda, exp_fwdb;

  always_comb begin
    r      = (op == 6'b000000);
    i_and  = r &  func[5] & ~func[4] & ~func[3] &  func[2] & ~func[1] & ~func[0];
    i_or   = r &  func[5] & ~func[4] & ~func[3] &  func[2] & ~func[1] &  func[0];
    i_xor  = r &  func[5] & ~func[4] & ~func[3] &  func[2] &  func[1] & ~func[0];
    i_add  = r &  func[5] & ~func[4] & ~func[3] & ~func[2] & ~func[1] & ~func[0];
    i_sub  = r &  func[5] & ~func[4] & ~func[3] & ~func[2] &  func[1] & ~func[0];
    i_sll  = r & ~func[5] & ~func[4] & ~func[3] & ~func[2] & ~func[1] & ~func[0];
    i_srl  = r & ~func[5] & ~func[4] & ~func[3] & ~func[2] &  func[1] & ~func[0];
    i_sra  = r & ~func[5] & ~func[4] & ~func[3] & ~func[2] &  func[1] &  func[0];
    i_jr   = r & ~func[5] & ~func[4] &  func[3] & ~func[2] & ~func[1] & ~func[0];
    i_j    = ~op[5] & ~op[4] & ~op[3] & ~op[2] &  op[1] & ~op[0];
    i_jal  = ~op[5] & ~op[4] & ~op[3] & ~op[2] &  op[1] &  op[0];
    i_addi = ~op[5] & ~op[4] &  op[3] & ~op[2] & ~op[1] & ~op[0];
    i_andi = ~op[5] & ~op[4] &  op[3] &  op[2] & ~op[1] & ~op[0];
    i_ori  = ~op[5] & ~op[4] &  op[3] &  op[2] & ~op[1] &  op[0];
    i_xori = ~op[5] & ~op[4] &  op[3] &  op[2] &  op[1] & ~op[0];
    i_lw   =  op[5] & ~op[4] & ~op[3] & ~op[2] &  op[1] &  op[0];
    i_sw   =  op[5] & ~op[4] &  op[3] & ~op[2] &  op[1] &  op[0];
    i_beq  = ~op[5] & ~op[4] & ~op[3] &  op[2] & ~op[1] & ~op[0];
    i_bne  = ~op[5] & ~op[4] & ~op[3] &  op[2] & ~op[1] &  op[0];
    i_lui  = ~op[5] & ~op[4] &  op[3] &  op[2] &  op[1] &  op[0];

    i_rs   = i_add|i_sub|i_and|i_or|i_xor|i_jr|i_addi|i_andi|i_ori|i_xori|i_lw|i_sw|i_beq|i_bne;
    i_rt   = i_add|i_sub|i_and|i_or|i_xor|i_sll|i_srl|i_sra|i_sw|i_beq|i_bne;

    exp_daluc[3] = i_sra;
    exp_daluc[2] = i_sub|i_beq|i_bne|i_or|i_ori|i_lui|i_srl|i_sra;
    exp_daluc[1] = i_xor|i_xori|i_lui|i_sll|i_srl|i_sra;
    exp_daluc[0] = i_and|i_andi|i_or|i_ori|i_sll|i_srl|i_sra;

    exp_wpcir = ~(ewreg & em2reg & (ern!=5'd0) & ((i_rs & (ern==rs)) | (i_rt & (ern==rt))));
    exp_wreg  = (i_add|i_sub|i_and|i_or|i_xor|i_sll|i_srl|i_sra|i_addi|i_andi|i_ori|i_xori|i_lw|i_lui|i_jal) & exp_wpcir;
    exp_wmem  = i_sw & exp_wpcir;
    exp_m2reg = i_lw;
    exp_jal   = i_jal;
    exp_aluimm= i_addi|i_andi|i_ori|i_xori|i_lui|i_sw|i_lw;
    exp_shift = i_sll|i_srl|i_sra;
    exp_regrt = i_lui|i_addi|i_andi|i_ori|i_xori|i_lw;
    exp_sext  = i_lui|i_addi|i_lw|i_sw|i_beq|i_bne;

    exp_pcsource[1] = i_j|i_jr|i_jal;
    exp_pcsource[0] = (i_beq & rsrtequ) | (i_bne & ~rsrtequ) | i_j | i_jal;

    automatic logic e_rs = ewreg & (ern!=5'd0) & (ern==rs);
    automatic logic m_rs0= mwreg & (mrn!=5'd0) & (mrn==rs) & ~mm2reg;
    automatic logic m_rs1= mwreg & (mrn!=5'd0) & (mrn==rs) &  mm2reg;
    automatic logic e_rt = ewreg & (ern!=5'd0) & (ern==rt);
    automatic logic m_rt0= mwreg & (mrn!=5'd0) & (mrn==rt) & ~mm2reg;
    automatic logic m_rt1= mwreg & (mrn!=5'd0) & (mrn==rt) &  mm2reg;

    exp_fwda = (e_rs & ~em2reg) ? 2'b01 :
               (m_rs0)          ? 2'b10 :
               (m_rs1)          ? 2'b11 : 2'b00;

    exp_fwdb = (e_rt & ~em2reg) ? 2'b01 :
               (m_rt0)          ? 2'b10 :
               (m_rt1)          ? 2'b11 : 2'b00;

    // X/Z checks on outputs
    assert (!$isunknown({wpcir,wreg,wmem,m2reg,jal,aluimm,shift,regrt,sext,daluc,pcsource,fwda,fwdb}))
      else $error("control_unit outputs contain X/Z");

    // Decode sanity: at most one instruction kind active
    assert ($onehot0({
      i_and,i_or,i_xor,i_add,i_sub,i_addi,i_andi,i_ori,i_xori,
      i_lw,i_sw,i_beq,i_bne,i_sll,i_srl,i_sra,i_jr,i_j,i_jal,i_lui
    })) else $error("Overlapping instruction decodes");

    // Output equivalence assertions
    assert (wpcir  === exp_wpcir)  else $error("wpcir mismatch");
    assert (wreg   === exp_wreg)   else $error("wreg mismatch");
    assert (wmem   === exp_wmem)   else $error("wmem mismatch");
    assert (m2reg  === exp_m2reg)  else $error("m2reg mismatch");
    assert (jal    === exp_jal)    else $error("jal mismatch");
    assert (aluimm === exp_aluimm) else $error("aluimm mismatch");
    assert (shift  === exp_shift)  else $error("shift mismatch");
    assert (regrt  === exp_regrt)  else $error("regrt mismatch");
    assert (sext   === exp_sext)   else $error("sext mismatch");
    assert (daluc  === exp_daluc)  else $error("daluc mismatch");
    assert (pcsource === exp_pcsource) else $error("pcsource mismatch");
    assert (fwda   === exp_fwda)   else $error("fwda mismatch");
    assert (fwdb   === exp_fwdb)   else $error("fwdb mismatch");

    // Stall gating safety
    assert ((!wpcir) -> (!wreg && !wmem))
      else $error("wpcir low must gate off wreg/wmem");

    // Forwarding priority checks
    assert (((ewreg && (ern!=0) && (ern==rs) && !em2reg)) -> (fwda==2'b01))
      else $error("fwda priority to E-stage violated");
    assert (((ewreg && (ern!=0) && (ern==rt) && !em2reg)) -> (fwdb==2'b01))
      else $error("fwdb priority to E-stage violated");
    assert ((((mwreg && (mrn!=0) && (mrn==rs) && !mm2reg)) && !(ewreg && (ern!=0) && (ern==rs) && !em2reg)) -> (fwda==2'b10))
      else $error("fwda M-stage ALU forwarding violated");
    assert ((((mwreg && (mrn!=0) && (mrn==rt) && !mm2reg)) && !(ewreg && (ern!=0) && (ern==rt) && !em2reg)) -> (fwdb==2'b10))
      else $error("fwdb M-stage ALU forwarding violated");
    assert ((((mwreg && (mrn!=0) && (mrn==rs) &&  mm2reg)) && !(ewreg && (ern!=0) && (ern==rs) && !em2reg) && !(mwreg && (mrn!=0) && (mrn==rs) && !mm2reg)) -> (fwda==2'b11))
      else $error("fwda M-stage MEM forwarding violated");
    assert ((((mwreg && (mrn!=0) && (mrn==rt) &&  mm2reg)) && !(ewreg && (ern!=0) && (ern==rt) && !em2reg) && !(mwreg && (mrn!=0) && (mrn==rt) && !mm2reg)) -> (fwdb==2'b11))
      else $error("fwdb M-stage MEM forwarding violated");

    // pcsource encoding coverage assertions
    assert ((i_jr)  -> (pcsource==2'b10)) else $error("pcsource for jr must be 10");
    assert (((i_j|i_jal)) -> (pcsource==2'b11)) else $error("pcsource for j/jal must be 11");
    assert (((i_beq & rsrtequ) | (i_bne & ~rsrtequ)) -> (pcsource==2'b01))
      else $error("pcsource for taken branch must be 01");
  end

  // Coverage (light but complete)
  // Instruction decode coverage
  cover (i_and);  cover (i_or);   cover (i_xor);  cover (i_add);  cover (i_sub);
  cover (i_addi); cover (i_andi); cover (i_ori);  cover (i_xori);
  cover (i_lw);   cover (i_sw);   cover (i_beq);  cover (i_bne);
  cover (i_sll);  cover (i_srl);  cover (i_sra);  cover (i_jr);   cover (i_j); cover (i_jal); cover (i_lui);

  // Hazard/stall coverage
  cover (!wpcir);
  cover (ewreg && em2reg && (ern!=0) && i_rs && (ern==rs) && !wpcir);
  cover (ewreg && em2reg && (ern!=0) && i_rt && (ern==rt) && !wpcir);

  // Forwarding encodings
  cover (fwda==2'b00); cover (fwda==2'b01); cover (fwda==2'b10); cover (fwda==2'b11);
  cover (fwdb==2'b00); cover (fwdb==2'b01); cover (fwdb==2'b10); cover (fwdb==2'b11);

  // pcsource encodings
  cover (pcsource==2'b00);
  cover (pcsource==2'b01);
  cover (pcsource==2'b10);
  cover (pcsource==2'b11);

endmodule