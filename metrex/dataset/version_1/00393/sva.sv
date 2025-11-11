// SVA for Control_Unit
// Bind module. Focused, high-signal-quality assertions and coverage.
module Control_Unit_SVA (Control_Unit dut);

  // Default clocking/reset for assertions
  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (!dut.rst);

  // -----------------------------
  // Reset behavior
  // -----------------------------
  // Async reset forces state to _Idle and decode to 0
  a_reset_state: assert property (!dut.rst |-> dut.state == dut._Idle);
  a_reset_curins: assert property (!dut.rst |-> dut.cur_ins == 6'd0);

  // -----------------------------
  // State transitions
  // -----------------------------
  a_idle_to_ifetch: assert property (dut.state == dut._Idle  |=> dut.state == dut._IFetch);
  a_ifetch_to_idec: assert property (dut.state == dut._IFetch |=> dut.state == dut._IDec);
  a_idec_next:      assert property (dut.state == dut._IDec && (dut.cur_ins == dut.HLT) |=> dut.state == dut._Halt);
  a_idec_to_exec:   assert property (dut.state == dut._IDec && (dut.cur_ins != dut.HLT) |=> dut.state == dut._Exec);
  a_exec_to_mem:    assert property (dut.state == dut._Exec  |=> dut.state == dut._Mem);
  a_mem_branch_or_store_path: assert property (
      dut.state == dut._Mem &&
      (dut.cur_ins inside {dut.B, dut.BEQZ, dut.BNEZ, dut.BTEQZ, dut.BTNEZ, dut.SW, dut.SW_RS, dut.SW_SP, dut.JR, dut.JRRA})
      |=> dut.state == dut._IFetch
  );
  a_mem_default_to_wb: assert property (
      dut.state == dut._Mem &&
      !(dut.cur_ins inside {dut.B, dut.BEQZ, dut.BNEZ, dut.BTEQZ, dut.BTNEZ, dut.SW, dut.SW_RS, dut.SW_SP, dut.JR, dut.JRRA})
      |=> dut.state == dut._WB
  );
  a_wb_to_ifetch: assert property (dut.state == dut._WB |=> dut.state == dut._IFetch);
  a_halt_sticky:  assert property (dut.state == dut._Halt |=> dut.state == dut._Halt);

  // -----------------------------
  // Per-state output checks
  // -----------------------------
  // _Idle drives all known defaults
  a_idle_outputs: assert property (
    dut.state == dut._Idle |->
      !dut.Load_NPC && !dut.Load_PC && !dut.Load_IR &&
      !dut.Load_RegA && !dut.Load_RegB && !dut.Load_Imm &&
      !dut.WT_Reg && (dut.Addr_Reg == 4'b0) && (dut.Extend == 3'b0) &&
      (dut.Send_Reg == 8'b0) && !dut.Load_LMD && !dut.Cond_Kind &&
      (dut.Jump_Kind == 2'b00) && !dut.Sel_Mux1 && !dut.Sel_Mux2 &&
      (dut.Sel_Mux4 == 2'b00) && (dut.Cal_ALU == 5'b0) &&
      !dut.Write && !dut.Load_ALU
  );

  // _IFetch
  a_ifetch_outputs: assert property (
    dut.state == dut._IFetch |->
      !dut.Write && !dut.Load_LMD && !dut.WT_Reg && !dut.Load_PC &&
      dut.Load_IR && dut.Load_NPC
  );

  // _IDec
  a_idec_basic: assert property (
    dut.state == dut._IDec |->
      !dut.Load_IR && !dut.Load_NPC &&
      dut.Load_RegA && dut.Load_RegB && dut.Load_Imm
  );

  // _Exec
  a_exec_basic: assert property (
    dut.state == dut._Exec |->
      !dut.Load_RegA && !dut.Load_RegB && !dut.Load_Imm &&
      dut.Load_ALU
  );

  // _Mem
  a_mem_basic: assert property (dut.state == dut._Mem |->
      !dut.Load_ALU && dut.Load_PC
  );

  // _WB
  a_wb_basic: assert property (dut.state == dut._WB |->
      !dut.Write && !dut.Load_LMD && !dut.Load_PC && dut.WT_Reg
  );

  // -----------------------------
  // Decode: IR -> cur_ins mapping
  // -----------------------------
  // Top-level opcodes
  a_dec_ADDIU:  assert property ((dut.IR_in[15:11] == 5'b01001) |-> dut.cur_ins == dut.ADDIU);
  a_dec_ADDIU3: assert property ((dut.IR_in[15:11] == 5'b01000) |-> dut.cur_ins == dut.ADDIU3);
  a_dec_ADDSP3: assert property ((dut.IR_in[15:11] == 5'b00000) |-> dut.cur_ins == dut.ADDSP3);
  a_dec_B:      assert property ((dut.IR_in[15:11] == 5'b00010) |-> dut.cur_ins == dut.B);
  a_dec_BEQZ:   assert property ((dut.IR_in[15:11] == 5'b00100) |-> dut.cur_ins == dut.BEQZ);
  a_dec_BNEZ:   assert property ((dut.IR_in[15:11] == 5'b00101) |-> dut.cur_ins == dut.BNEZ);
  a_dec_CMPI:   assert property ((dut.IR_in[15:11] == 5'b01110) |-> dut.cur_ins == dut.CMPI);
  a_dec_INT:    assert property ((dut.IR_in[15:11] == 5'b11111) |-> dut.cur_ins == dut.INT);
  a_dec_LI:     assert property ((dut.IR_in[15:11] == 5'b01101) |-> dut.cur_ins == dut.LI);
  a_dec_LW:     assert property ((dut.IR_in[15:11] == 5'b10011) |-> dut.cur_ins == dut.LW);
  a_dec_LW_SP:  assert property ((dut.IR_in[15:11] == 5'b10010) |-> dut.cur_ins == dut.LW_SP);
  a_dec_MOVE:   assert property ((dut.IR_in[15:11] == 5'b01111) |-> dut.cur_ins == dut.MOVE);
  a_dec_NOP:    assert property ((dut.IR_in[15:11] == 5'b00001) |-> dut.cur_ins == dut.NOP);
  a_dec_SLTI:   assert property ((dut.IR_in[15:11] == 5'b01010) |-> dut.cur_ins == dut.SLTI);
  a_dec_SLTUI:  assert property ((dut.IR_in[15:11] == 5'b01011) |-> dut.cur_ins == dut.SLTUI);
  a_dec_SW:     assert property ((dut.IR_in[15:11] == 5'b11011) |-> dut.cur_ins == dut.SW);
  a_dec_SW_SP:  assert property ((dut.IR_in[15:11] == 5'b11010) |-> dut.cur_ins == dut.SW_SP);
  a_dec_HLT:    assert property ((dut.IR_in[15:11] == 5'b10000) |-> dut.cur_ins == dut.HLT);

  // 00110 sub-op
  a_dec_SLL: assert property ((dut.IR_in[15:11] == 5'b00110) && (dut.IR_in[1:0] == 2'b00) |-> dut.cur_ins == dut.SLL);
  a_dec_SRA: assert property ((dut.IR_in[15:11] == 5'b00110) && (dut.IR_in[1:0] == 2'b11) |-> dut.cur_ins == dut.SRA);
  a_dec_SRL: assert property ((dut.IR_in[15:11] == 5'b00110) && (dut.IR_in[1:0] == 2'b10) |-> dut.cur_ins == dut.SRL);

  // 01100 sub-op via [10:8]
  a_dec_ADDSP: assert property ((dut.IR_in[15:11] == 5'b01100) && (dut.IR_in[10:8] == 3'b011) |-> dut.cur_ins == dut.ADDSP);
  a_dec_BTEQZ: assert property ((dut.IR_in[15:11] == 5'b01100) && (dut.IR_in[10:8] == 3'b000) |-> dut.cur_ins == dut.BTEQZ);
  a_dec_BTNEZ: assert property ((dut.IR_in[15:11] == 5'b01100) && (dut.IR_in[10:8] == 3'b001) |-> dut.cur_ins == dut.BTNEZ);
  a_dec_MTSP:  assert property ((dut.IR_in[15:11] == 5'b01100) && (dut.IR_in[10:8] == 3'b100) |-> dut.cur_ins == dut.MTSP);
  a_dec_SW_RS: assert property ((dut.IR_in[15:11] == 5'b01100) && (dut.IR_in[10:8] == 3'b010) |-> dut.cur_ins == dut.SW_RS);

  // 11100 sub-op via [1:0]
  a_dec_ADDU:  assert property ((dut.IR_in[15:11] == 5'b11100) && (dut.IR_in[1:0] == 2'b01) |-> dut.cur_ins == dut.ADDU);
  a_dec_SUBU:  assert property ((dut.IR_in[15:11] == 5'b11100) && (dut.IR_in[1:0] == 2'b11) |-> dut.cur_ins == dut.SUBU);

  // 11101 sub-op via [4:0] and nested [7:5]
  a_dec_AND:  assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b01100) |-> dut.cur_ins == dut.AND);
  a_dec_CMP:  assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b01010) |-> dut.cur_ins == dut.CMP);
  a_dec_NEG:  assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b01011) |-> dut.cur_ins == dut.NEG);
  a_dec_NOT:  assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b01111) |-> dut.cur_ins == dut.NOT);
  a_dec_OR:   assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b01101) |-> dut.cur_ins == dut.OR);
  a_dec_SLLV: assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00100) |-> dut.cur_ins == dut.SLLV);
  a_dec_SLT:  assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00010) |-> dut.cur_ins == dut.SLT);
  a_dec_SLTU: assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00011) |-> dut.cur_ins == dut.SLTU);
  a_dec_SRAV: assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00111) |-> dut.cur_ins == dut.SRAV);
  a_dec_SRLV: assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00110) |-> dut.cur_ins == dut.SRLV);
  a_dec_XOR:  assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b01110) |-> dut.cur_ins == dut.XOR);
  a_dec_JALR: assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00000) && (dut.IR_in[7:5] == 3'b110) |-> dut.cur_ins == dut.JALR);
  a_dec_JR:   assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00000) && (dut.IR_in[7:5] == 3'b000) |-> dut.cur_ins == dut.JR);
  a_dec_JRRA: assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00000) && (dut.IR_in[7:5] == 3'b001) |-> dut.cur_ins == dut.JRRA);
  a_dec_MFPC: assert property ((dut.IR_in[15:11] == 5'b11101) && (dut.IR_in[4:0] == 5'b00000) && (dut.IR_in[7:5] == 3'b010) |-> dut.cur_ins == dut.MFPC);

  // 11110 sub-op via [7:0]
  a_dec_MFIH: assert property ((dut.IR_in[15:11] == 5'b11110) && (dut.IR_in[7:0] == 8'b0000_0000) |-> dut.cur_ins == dut.MFIH);
  a_dec_MTIH: assert property ((dut.IR_in[15:11] == 5'b11110) && (dut.IR_in[7:0] == 8'b0000_0001) |-> dut.cur_ins == dut.MTIH);

  // -----------------------------
  // IDec control mapping
  // -----------------------------
  // Send_Reg
  a_idec_sendreg_g1: assert property (dut.state == dut._IDec &&
     (dut.cur_ins inside {dut.ADDIU,dut.ADDIU3,dut.BEQZ,dut.BNEZ,dut.CMPI,dut.JALR,dut.JR,dut.LW,dut.MTIH,dut.SLTI,dut.SLTUI})
     |->
     dut.Send_Reg == {1'b0, dut.IR_in[10:8], 4'b0}
  );
  a_idec_sendreg_g2: assert property (dut.state == dut._IDec &&
     (dut.cur_ins inside {dut.MOVE,dut.MTSP,dut.NOT,dut.SLL,dut.SRA,dut.SRL})
     |->
     dut.Send_Reg == {1'b0, dut.IR_in[7:5], 4'b0}
  );
  a_idec_sendreg_g3: assert property (dut.state == dut._IDec &&
     (dut.cur_ins inside {dut.ADDSP3,dut.ADDSP,dut.LW_SP})
     |->
     dut.Send_Reg == 8'hF0
  );
  a_idec_sendreg_g4: assert property (dut.state == dut._IDec &&
     (dut.cur_ins inside {dut.ADDU,dut.AND,dut.CMP,dut.OR,dut.SLLV,dut.SLT,dut.SLTU,dut.SRAV,dut.SRLV,dut.SUBU,dut.SW,dut.XOR})
     |->
     dut.Send_Reg == {1'b0, dut.IR_in[10:8], 1'b0, dut.IR_in[7:5]}
  );
  a_idec_sendreg_g5: assert property (dut.state == dut._IDec &&
     (dut.cur_ins inside {dut.B,dut.INT,dut.LI,dut.MFPC,dut.NOP})
     |->
     dut.Send_Reg == 8'h00
  );
  a_idec_sendreg_g6: assert property (dut.state == dut._IDec && dut.cur_ins == dut.JRRA |-> dut.Send_Reg == 8'h20);
  a_idec_sendreg_g7: assert property (dut.state == dut._IDec && dut.cur_ins == dut.MFIH |-> dut.Send_Reg == 8'hD0);
  a_idec_sendreg_g8: assert property (dut.state == dut._IDec && dut.cur_ins == dut.NEG  |-> dut.Send_Reg == {4'b0000,1'b0,dut.IR_in[7:5]});
  a_idec_sendreg_g9: assert property (dut.state == dut._IDec && dut.cur_ins == dut.SW_RS |-> dut.Send_Reg == 8'hF2);
  a_idec_sendreg_g10: assert property (dut.state == dut._IDec && dut.cur_ins == dut.SW_SP |-> dut.Send_Reg == {4'hF,1'b0,dut.IR_in[7:5]});
  a_idec_sendreg_g11: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.BTEQZ,dut.BTNEZ}) |-> dut.Send_Reg == 8'hE0);

  // Extend
  a_idec_extend_0: assert property (dut.state == dut._IDec &&
    (dut.cur_ins inside {dut.ADDIU,dut.ADDSP3,dut.ADDSP,dut.BEQZ,dut.BNEZ,dut.BTEQZ,dut.BTNEZ,dut.CMPI,dut.LW_SP,dut.SLTI,dut.SLTUI,dut.SW_RS,dut.SW_SP})
    |->
    dut.Extend == 3'd0
  );
  a_idec_extend_1: assert property (dut.state == dut._IDec && (dut.cur_ins == dut.ADDIU3) |-> dut.Extend == 3'd1);
  a_idec_extend_2: assert property (dut.state == dut._IDec && (dut.cur_ins == dut.B)      |-> dut.Extend == 3'd2);
  a_idec_extend_3: assert property (dut.state == dut._IDec && (dut.cur_ins == dut.INT)    |-> dut.Extend == 3'd3);
  a_idec_extend_4: assert property (dut.state == dut._IDec && (dut.cur_ins == dut.LI)     |-> dut.Extend == 3'd4);
  a_idec_extend_5: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.LW,dut.SW}) |-> dut.Extend == 3'd5);
  a_idec_extend_6: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.SLL,dut.SRA,dut.SRL}) |-> dut.Extend == 3'd6);

  // Sel_Mux1
  a_idec_mux1: assert property (dut.state == dut._IDec |->
      dut.Sel_Mux1 == (dut.cur_ins inside {dut.B, dut.BEQZ, dut.BNEZ, dut.BTEQZ, dut.BTNEZ, dut.MFPC})
  );

  // Sel_Mux2
  a_idec_mux2: assert property (dut.state == dut._IDec |->
      dut.Sel_Mux2 == (dut.cur_ins inside {
        dut.ADDIU,dut.ADDIU3,dut.ADDSP3,dut.ADDSP,
        dut.B,dut.BEQZ,dut.BNEZ,dut.BTEQZ,dut.BTNEZ,
        dut.CMPI,dut.INT,dut.LI,dut.LW,dut.LW_SP,
        dut.SLL,dut.SLTI,dut.SLTUI,dut.SRA,dut.SRL,
        dut.SW,dut.SW_RS,dut.SW_SP
      })
  );

  // Cal_ALU
  a_idec_cal_0: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.JALR,dut.JR,dut.JRRA,dut.MFIH,dut.MFPC,dut.MOVE,dut.MTIH,dut.MTSP}) |-> dut.Cal_ALU == 5'd0);
  a_idec_cal_1: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.INT,dut.LI}) |-> dut.Cal_ALU == 5'd1);
  a_idec_cal_2: assert property (dut.state == dut._IDec && (dut.cur_ins inside {
    dut.ADDIU,dut.ADDIU3,dut.ADDSP3,dut.ADDSP,dut.ADDU,
    dut.B,dut.BEQZ,dut.BNEZ,dut.BTEQZ,dut.BTNEZ,
    dut.LW,dut.LW_SP,dut.SW,dut.SW_RS,dut.SW_SP}) |-> dut.Cal_ALU == 5'd2);
  a_idec_cal_3: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.NEG,dut.SUBU}) |-> dut.Cal_ALU == 5'd3);
  a_idec_cal_4: assert property (dut.state == dut._IDec && dut.cur_ins == dut.AND |-> dut.Cal_ALU == 5'd4);
  a_idec_cal_5: assert property (dut.state == dut._IDec && dut.cur_ins == dut.OR  |-> dut.Cal_ALU == 5'd5);
  a_idec_cal_6: assert property (dut.state == dut._IDec && dut.cur_ins == dut.NOT |-> dut.Cal_ALU == 5'd6);
  a_idec_cal_7: assert property (dut.state == dut._IDec && dut.cur_ins == dut.XOR |-> dut.Cal_ALU == 5'd7);
  a_idec_cal_8: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.CMP,dut.CMPI}) |-> dut.Cal_ALU == 5'd8);
  a_idec_cal_9:  assert property (dut.state == dut._IDec && dut.cur_ins == dut.SLLV |-> dut.Cal_ALU == 5'd9);
  a_idec_cal_10: assert property (dut.state == dut._IDec && dut.cur_ins == dut.SRLV |-> dut.Cal_ALU == 5'd10);
  a_idec_cal_11: assert property (dut.state == dut._IDec && dut.cur_ins == dut.SLL  |-> dut.Cal_ALU == 5'd11);
  a_idec_cal_12: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.SLTU,dut.SLTUI}) |-> dut.Cal_ALU == 5'd12);
  a_idec_cal_13: assert property (dut.state == dut._IDec && dut.cur_ins == dut.SRAV |-> dut.Cal_ALU == 5'd13);
  a_idec_cal_14: assert property (dut.state == dut._IDec && dut.cur_ins == dut.SRL  |-> dut.Cal_ALU == 5'd14);
  a_idec_cal_15: assert property (dut.state == dut._IDec && dut.cur_ins == dut.SRA  |-> dut.Cal_ALU == 5'd15);
  a_idec_cal_16: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.SLT,dut.SLTI}) |-> dut.Cal_ALU == 5'd16);

  // Cond_Kind (only for conditional branches)
  a_idec_cond_eq: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.BEQZ,dut.BTEQZ}) |-> dut.Cond_Kind == 1'b0);
  a_idec_cond_ne: assert property (dut.state == dut._IDec && (dut.cur_ins inside {dut.BNEZ,dut.BTNEZ}) |-> dut.Cond_Kind == 1'b1);

  // Jump_Kind
  a_idec_jump_kind: assert property (dut.state == dut._IDec |->
    dut.Jump_Kind ==
      ( (dut.cur_ins inside {dut.BEQZ,dut.BNEZ,dut.BTEQZ,dut.BTNEZ}) ? 2'b10 :
        (dut.cur_ins inside {dut.B,dut.INT,dut.JALR,dut.JR,dut.JRRA}) ? 2'b11 :
        2'b00 )
  );

  // -----------------------------
  // Mem-stage controls
  // -----------------------------
  // Write and Load_LMD strobes and Sel_Mux4 mux steering
  a_mem_write:   assert property (dut.state == dut._Mem |->
      dut.Write == (dut.cur_ins inside {dut.SW, dut.SW_RS, dut.SW_SP})
  );
  a_mem_loadlmd: assert property (dut.state == dut._Mem |->
      dut.Load_LMD == (dut.cur_ins inside {dut.LW, dut.LW_SP})
  );
  a_mem_selmux4: assert property (dut.state == dut._Mem |->
      dut.Sel_Mux4 == (dut.cur_ins inside {dut.LW,dut.LW_SP} ? 2'd1 :
                       dut.cur_ins inside {dut.INT,dut.JALR}  ? 2'd2 : 2'd0)
  );

  // Addr_Reg mapping
  a_mem_addr_g1: assert property (dut.state == dut._Mem &&
    (dut.cur_ins inside {dut.ADDIU,dut.ADDSP3,dut.AND,dut.LI,dut.LW_SP,dut.MFIH,dut.MFPC,dut.MOVE,dut.NEG,dut.NOT,dut.OR,dut.SLL,dut.SRA,dut.SRL,dut.XOR})
    |->
    dut.Addr_Reg == {1'b0, dut.IR_in[10:8]}
  );
  a_mem_addr_g2: assert property (dut.state == dut._Mem &&
    (dut.cur_ins inside {dut.ADDIU3,dut.LW,dut.SLLV,dut.SRAV,dut.SRLV})
    |->
    dut.Addr_Reg == {1'b0, dut.IR_in[7:5]}
  );
  a_mem_addr_g3: assert property (dut.state == dut._Mem &&
    (dut.cur_ins inside {dut.ADDSP,dut.MTSP})
    |->
    dut.Addr_Reg == 4'b1111
  );
  a_mem_addr_g4: assert property (dut.state == dut._Mem &&
    (dut.cur_ins inside {dut.ADDU,dut.SUBU})
    |->
    dut.Addr_Reg == {1'b0, dut.IR_in[4:2]}
  );
  a_mem_addr_g5: assert property (dut.state == dut._Mem &&
    (dut.cur_ins inside {dut.CMP,dut.CMPI,dut.SLT,dut.SLTI,dut.SLTU,dut.SLTUI})
    |->
    dut.Addr_Reg == 4'b1110
  );
  a_mem_addr_g6: assert property (dut.state == dut._Mem && (dut.cur_ins inside {dut.INT,dut.JALR}) |->
    dut.Addr_Reg == 4'b0010
  );
  a_mem_addr_g7: assert property (dut.state == dut._Mem && (dut.cur_ins == dut.MTIH) |->
    dut.Addr_Reg == 4'b1101
  );

  // -----------------------------
  // Signal-location sanity: exclusivity
  // -----------------------------
  a_only_ifetch_load_ir_npc: assert property ((dut.Load_IR || dut.Load_NPC) |-> dut.state == dut._IFetch);
  a_only_exec_load_alu:      assert property (dut.Load_ALU |-> dut.state == dut._Exec);
  a_only_mem_load_pc:        assert property (dut.Load_PC  |-> dut.state == dut._Mem);
  a_only_mem_write:          assert property (dut.Write    |-> dut.state == dut._Mem);
  a_only_mem_loadlmd:        assert property (dut.Load_LMD |-> dut.state == dut._Mem);
  a_only_wb_wtreg:           assert property (dut.WT_Reg   |-> dut.state == dut._WB);

  // -----------------------------
  // Coverage
  // -----------------------------
  // Instruction coverage (1..45 are used for cur_ins encodings)
  genvar i;
  generate
    for (i = 1; i <= 45; i++) begin : cov_all_ins
      c_curins: cover property (dut.cur_ins == i);
    end
  endgenerate

  // State-flow coverage
  c_full_flow: cover property (
    dut.state == dut._Idle ##1 dut.state == dut._IFetch ##1 dut.state == dut._IDec
    ##1 dut.state == dut._Exec ##1 dut.state == dut._Mem ##1 dut.state == dut._WB ##1 dut.state == dut._IFetch
  );
  c_branch_flow: cover property (
    dut.state == dut._IDec && (dut.cur_ins inside {dut.B, dut.BEQZ, dut.BNEZ, dut.BTEQZ, dut.BTNEZ})
    ##1 dut.state == dut._Exec ##1 dut.state == dut._Mem ##1 dut.state == dut._IFetch
  );
  c_store_flow: cover property (
    dut.state == dut._IDec && (dut.cur_ins inside {dut.SW, dut.SW_RS, dut.SW_SP})
    ##1 dut.state == dut._Exec ##1 dut.state == dut._Mem && dut.Write ##1 dut.state == dut._IFetch
  );
  c_load_flow: cover property (
    dut.state == dut._IDec && (dut.cur_ins inside {dut.LW, dut.LW_SP})
    ##1 dut.state == dut._Exec ##1 dut.state == dut._Mem && dut.Load_LMD ##1 dut.state == dut._WB && dut.WT_Reg
  );
  c_halt: cover property (dut.state == dut._IDec && dut.cur_ins == dut.HLT ##1 dut.state == dut._Halt);

endmodule

// Example bind (uncomment if you want to auto-bind for all instances)
// bind Control_Unit Control_Unit_SVA SVA_Control_Unit(.dut(this));