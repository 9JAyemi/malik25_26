// SVA for cpu_ctl. Bind this module to the DUT instance.
// Focused, clockless concurrent SVA for combinational control logic.

module cpu_ctl_sva (
  input  logic [5:0] op, func,
  input  logic       equal_result,
  input  logic       JR, J, JAL, LW, WREG, WMEM, RDorRT, SE, SA, IorR, BJ,
  input  logic [4:0] Aluc
);
  // Recompute decodes (golden)
  logic r_type, i_jr, i_sll, i_srl, i_sra;
  logic i_addi, i_addiu, i_andi, i_ori, i_xori, i_lui, i_lw, i_sw, i_slti, i_sltiu;
  logic b_type, i_beq, i_bne;
  logic i_j, i_jal, i_type;

  assign r_type = (op == 6'b000000);
  assign i_jr   = r_type & (func == 6'b001000);
  assign i_sll  = r_type & (func == 6'b000000);
  assign i_srl  = r_type & (func == 6'b000010);
  assign i_sra  = r_type & (func == 6'b000011);

  assign i_addi  = (op == 6'b001000);
  assign i_addiu = (op == 6'b001001);
  assign i_andi  = (op == 6'b001100);
  assign i_ori   = (op == 6'b001101);
  assign i_xori  = (op == 6'b001110);
  assign i_lui   = (op == 6'b001111);
  assign i_lw    = (op == 6'b100011);
  assign i_sw    = (op == 6'b101011);
  assign i_slti  = (op == 6'b001010);
  assign i_sltiu = (op == 6'b001011);

  assign i_beq   = (op == 6'b000100);
  assign i_bne   = (op == 6'b000101);
  assign b_type  = i_beq | i_bne;

  assign i_j     = (op == 6'b000010);
  assign i_jal   = (op == 6'b000011);

  assign i_type  = i_addi | i_addiu | i_andi | i_ori | i_xori | i_lui | i_lw | i_sw | i_slti | i_sltiu;

  // Expected outputs
  logic expJR, expJ, expJAL, expLW, expWREG, expWMEM, expRDorRT, expSE, expSA, expIorR, expBJ;
  assign expJR     = i_jr;
  assign expJ      = i_j;
  assign expJAL    = i_jal;
  assign expLW     = i_lw;
  assign expWMEM   = i_sw;
  assign expRDorRT = r_type & ~i_jr;
  assign expSE     = i_addi | i_addiu | i_lw | i_sw | i_slti;
  assign expSA     = i_sll | i_srl | i_sra;
  assign expIorR   = i_type & ~b_type;
  assign expBJ     = (i_beq &  equal_result) | (i_bne & ~equal_result);
  assign expWREG   = i_jal | (expIorR & ~i_sw) | (r_type & ~i_jr);

  // Expected ALUC (note: DUT currently compares {op,func} to 6'b constants; this check enforces intended mapping)
  logic [3:0] expAluc4;
  always_comb begin
    if (r_type) expAluc4 = func[3:0];
    else unique case (op)
      6'b001000: expAluc4 = 4'b0010; // ADDI
      6'b001001: expAluc4 = 4'b0011; // ADDIU
      6'b001100: expAluc4 = 4'b0000; // ANDI
      6'b001101: expAluc4 = 4'b0101; // ORI
      6'b001110: expAluc4 = 4'b0110; // XORI
      6'b001010: expAluc4 = 4'b0111; // SLTI
      6'b001011: expAluc4 = 4'b1000; // SLTIU
      6'b100011: expAluc4 = 4'b0001; // LW
      6'b101011: expAluc4 = 4'b0001; // SW
      default:   expAluc4 = 4'b0000;
    endcase
  end

  // Core equivalence checks (clockless concurrent properties)
  assert property (JR     == expJR);
  assert property (J      == expJ);
  assert property (JAL    == expJAL);
  assert property (LW     == expLW);
  assert property (WMEM   == expWMEM);
  assert property (RDorRT == expRDorRT);
  assert property (SE     == expSE);
  assert property (SA     == expSA);
  assert property (IorR   == expIorR);
  assert property (BJ     == expBJ);
  assert property (WREG   == expWREG);

  // ALU control correctness and width sanity
  assert property (Aluc[3:0] == expAluc4 && Aluc[4] == 1'b0);

  // Disjointness/sanity of decodes
  assert property ($onehot0({i_beq, i_bne}));
  assert property ($onehot0({i_j, i_jal}));
  assert property ($onehot0({i_sll, i_srl, i_sra}));
  assert property ($onehot0({i_addi,i_addiu,i_andi,i_ori,i_xori,i_lui,i_lw,i_sw,i_slti,i_sltiu}));
  assert property ($onehot0({r_type, i_type, b_type, i_j, i_jal}));

  // No X on primary control outputs
  assert property (!$isunknown({JR,J,JAL,LW,WREG,WMEM,RDorRT,SE,SA,IorR,BJ,Aluc}));

  // Key functional covers
  cover property (r_type);
  cover property (i_addi);  cover property (i_addiu);
  cover property (i_andi);  cover property (i_ori);  cover property (i_xori); cover property (i_lui);
  cover property (i_slti);  cover property (i_sltiu);
  cover property (i_lw && LW && WREG);
  cover property (i_sw && WMEM && !WREG);
  cover property (i_j  && J);
  cover property (i_jal && JAL && WREG);
  cover property (i_jr && JR && !RDorRT);
  cover property (i_sll && SA); cover property (i_srl && SA); cover property (i_sra && SA);

  // Branch outcomes
  cover property (i_beq &&  equal_result &&  BJ);
  cover property (i_beq && !equal_result && !BJ);
  cover property (i_bne &&  equal_result && !BJ);
  cover property (i_bne && !equal_result &&  BJ);
endmodule

// Bind into DUT
bind cpu_ctl cpu_ctl_sva cpu_ctl_sva_b (
  .op(op), .func(func), .equal_result(equal_result),
  .JR(JR), .J(J), .JAL(JAL), .LW(LW), .WREG(WREG), .WMEM(WMEM),
  .RDorRT(RDorRT), .SE(SE), .SA(SA), .IorR(IorR), .BJ(BJ),
  .Aluc(Aluc)
);