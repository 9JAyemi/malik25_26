// SVA for CONFIG_REGS
module CONFIG_REGS_sva;
  default clocking cb @(posedge BCLK); endclocking
  default disable iff (!BRESET);

  // Reset levels (override disable to actually check reset)
  assert property (disable iff (1'b0) (@(posedge BCLK) !BRESET |-> (CFG==13'h0 && MCR==4'h0 && dcr==13'd0 && DSR==4'd0)));

  // Register loads
  assert property (ld_cfg |=> CFG == $past(SRC1[12:0]));
  assert property (ld_mcr |=> MCR == $past(SRC1[3:0]));
  // PTB/IVAR pipeline
  assert property (ivarreg == $past(op_ok & (WRADR[5:1]==5'd7) & WREN));
  assert property (PTB_WR  == $past(op_ok & (WRADR[5:1]==5'd6) & WREN));
  assert property (PTB_SEL == $past(WRADR[0]));
  assert property (IVAR[1] == ivarreg);
  assert property (IVAR[0] == PTB_SEL);

  // CINV path
  assert property (old_cfg == $past({CFG[11],CFG[9]}));
  assert property (ci_all  == $past((do_cinv &  WRADR[2]) ? WRADR[1:0] : 2'b0));
  assert property (ci_line == $past((do_cinv & ~WRADR[2]) ? WRADR[1:0] : 2'b0));
  assert property (init_ic == (old_cfg[1] & (~CFG[11] | ci_all[1])));
  assert property (init_dc == (old_cfg[0] & (~CFG[9]  | ci_all[0])));
  assert property (CINV    == {init_ic,ci_line[1],init_dc,ci_line[0]});
  assert property (check_y == $past(ld_cfg | do_cinv));
  assert property (Y_INIT  == (check_y & ~init_ic & ~init_dc));

  // Debug control regs
  assert property (ld_dcr |=> dcr == $past({SRC1[23:19],SRC1[7:0]}));
  assert property (!ld_dcr |-> $stable(dcr));
  assert property (ld_bpc |=> bpc == $past(SRC1));
  assert property (!ld_bpc |-> $stable(bpc));
  assert property (ld_car |=> car == $past(SRC1[31:2]));
  assert property (!ld_car |-> $stable(car));

  // DBG bus and traps
  assert property (DBG_IN == {(dcr[12]&dcr[11]),(dcr[12]&dcr[10]),(dcr[7]&dcr[6]),(dcr[7]&dcr[5]),dcr[4:0],car});
  assert property (DBG_TRAPS[0] == ((dcr[12] & (USER ? dcr[10] : dcr[11])) & dcr[9] & (PC_ARCHI == bpc)));
  assert property (DBG_TRAPS[1] == DBG_HIT);
  assert property (DBG_TRAPS[2] == dcr[8]);

  // DSR updates (when not loading DSR)
  assert property (ld_dsr |=> DSR == $past(SRC1[31:28]));
  assert property (!ld_dsr |-> (DSR[3] == ($past(DBG_HIT) ? $past(READ) : $past(DSR[3]))));
  assert property (!ld_dsr |-> (DSR[2] == $past(DSR[2] | PCMATCH)));
  assert property (!ld_dsr |-> (DSR[1] == $past(DSR[1])));
  assert property (!ld_dsr |-> (DSR[0] == $past(DSR[0] | DBG_HIT)));

  // Coverage
  cover property (ld_cfg ##1 Y_INIT);
  cover property (do_cinv &&  WRADR[2] && WRADR[1] && WRADR[0]);
  cover property (do_cinv && !WRADR[2] && WRADR[1] && WRADR[0]);
  cover property (op_ok && (WRADR[5:1]==5'd6) && WREN);
  cover property (op_ok && (WRADR[5:1]==5'd7) && WREN);
  cover property (ld_dcr ##1 ld_bpc ##1 ld_car ##1 DBG_TRAPS[0]);
endmodule

bind CONFIG_REGS CONFIG_REGS_sva sva_CONFIG_REGS_inst();


// SVA for FP_STAT_REG
module FP_STAT_REG_sva;
  default clocking cb @(posedge BCLK); endclocking
  default disable iff (!BRESET);

  // Reset levels
  assert property (disable iff (1'b0) (@(posedge BCLK) !BRESET |-> (FPU_TRAP==1'b0 && flags==5'b0 && rm_bit==1'b0 && set_bits==11'b0)));

  // Control/status wires
  assert property (TWREN == ~((UP_SP && (TT_SP[2:0]!=3'b0)) || (UP_DP && (TT_DP[2:0]!=3'b0))));
  assert property (update  == (update_d & ~FPU_TRAP));
  assert property (SAVE_PC == ((UP_SP | UP_DP) & ~FPU_TRAP));

  // Pipeline regs
  assert property (update_d == $past(update_i));
  assert property (trap_d   == $past((UP_SP ? TT_SP[4:3] : TT_DP[4:3])));
  assert property (set_rm_d == $past(WREN && (WRADR==2'b10)));

  // FPU_TRAP pulse behavior
  assert property ($past(TWREN) |-> (FPU_TRAP==1'b0));
  assert property (($past(!TWREN) && !$past(FPU_TRAP)) |-> (FPU_TRAP==1'b1));
  assert property ($past(FPU_TRAP) |-> (FPU_TRAP==1'b0));

  // Flag updates [4]=iflag, [3]=uflag
  assert property (load_fsr |=> flags[4:3] == $past({DIN[6],DIN[4]}));
  assert property (!load_fsr && update |-> flags[4:3] == {((update & trap_d[4]) | flags[4]), ((update & trap_d[3]) | flags[3])});
  assert property (!(load_fsr || update) |-> $stable(flags[4:3]));

  // Flags[2:0]
  assert property (load_fsr |=> flags[2:0] == $past(DIN[2:0]));
  assert property (!load_fsr && update_i |-> flags[2:0] == $past((UP_SP ? TT_SP[2:0] : TT_DP[2:0])));
  assert property (!(load_fsr || update_i) |-> $stable(flags[2:0]));

  // rm_bit and set_bits
  assert property (load_fsr |=> rm_bit == $past(DIN[16]));
  assert property (!load_fsr && set_rm_d && !FPU_TRAP |-> rm_bit == 1'b1);
  assert property (!(load_fsr || (set_rm_d && !FPU_TRAP)) |-> $stable(rm_bit));
  assert property (load_fsr |=> set_bits == $past({DIN[15:7],DIN[5],DIN[3]}));
  assert property (!load_fsr |-> $stable(set_bits));

  // Encoded outputs
  assert property (FSR == {15'h0, ((set_rm_d & ~FPU_TRAP) | rm_bit),
                           set_bits[10:2],
                           ((update & trap_d[4]) | flags[4]),
                           set_bits[1],
                           ((update & trap_d[3]) | flags[3]),
                           set_bits[0],
                           flags[2:0]});

  // Coverage
  cover property (load_fsr);
  cover property (update_i);
  cover property (!TWREN ##1 FPU_TRAP);
  cover property (set_rm_d && !FPU_TRAP);
  cover property (SAVE_PC);
endmodule

bind FP_STAT_REG FP_STAT_REG_sva sva_FP_STAT_REG_inst();


// SVA for REGISTER
module REGISTER_sva;
  default clocking cb @(posedge BCLK); endclocking

  // Derived signals
  assert property (BE == {WMASKE[1], WMASKE[1], (WMASKE[1] || WMASKE[0]), 1'b1});
  assert property (eq_rw == (ENWR && (RADR[5:0]==WADR)));

  // Read side latches
  assert property ($past(RADR[7]) |-> (MX == ($past(BE[2:0] & {3{$past(eq_rw)}}))));
  assert property ($past(RADR[7]) |-> (SELI == $past(RADR[6])));

  // DOUT mux
  assert property (DOUT[31:16] == (MX[2] ? BYDIN[31:16] : RF[31:16]));
  assert property (DOUT[15:8]  == (MX[1] ? BYDIN[15:8]  : RF[15:8]));
  assert property (DOUT[7:0]   == (MX[0] ? BYDIN[7:0]   : RF[7:0]));

  // RF read capture
  assert property ($past(RADR[7]) |-> (RF[31:24] == REGFILE_D[$past(RADR[5:0])] &&
                                       RF[23:16] == REGFILE_C[$past(RADR[5:0])] &&
                                       RF[15:8]  == REGFILE_B[$past(RADR[5:0])] &&
                                       RF[7:0]   == REGFILE_A[$past(RADR[5:0])]));

  // Writes
  assert property ($past(DOWR && BE[3]) |-> REGFILE_D[$past(WADR)] == $past(DIN[31:24]));
  assert property ($past(DOWR && BE[2]) |-> REGFILE_C[$past(WADR)] == $past(DIN[23:16]));
  assert property ($past(DOWR && BE[1]) |-> REGFILE_B[$past(WADR)] == $past(DIN[15:8]));
  assert property ($past(DOWR && BE[0]) |-> REGFILE_A[$past(WADR)] == $past(DIN[7:0]));

  // Coverage
  cover property (DOWR && BE==4'b1111);
  cover property ($past(RADR[7]) && $past(eq_rw) && (MX!=3'b000));
endmodule

bind REGISTER REGISTER_sva sva_REGISTER_inst();