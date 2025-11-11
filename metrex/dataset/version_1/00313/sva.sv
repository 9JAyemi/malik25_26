// Add this SVA block inside scheduler1_commit_entry (non-synthesizable)
`ifndef SYNTHESIS
`ifdef ASSERT_ON
    default clocking cb @(posedge iCLOCK); endclocking
    default disable iff (!inRESET);

    // Shorthands
    let cond0 = (!iLOCK && (b_state==2'h0) && iREGIST_0_VALID && (ENTRY_ID[5:0] == iREGIST_POINTER));
    let cond1 = (!iLOCK && (b_state==2'h0) && iREGIST_1_VALID && (ENTRY_ID[5:0] == (iREGIST_POINTER + 6'h1)));
    let wish0 = ((b_state==2'h0) && iREGIST_0_VALID && (ENTRY_ID[5:0] == iREGIST_POINTER));
    let wish1 = ((b_state==2'h0) && iREGIST_1_VALID && (ENTRY_ID[5:0] == (iREGIST_POINTER + 6'h1)));
    let ex_hit = (iEXEND_ALU0_VALID && (iEXEND_ALU0_COMMIT_TAG==ENTRY_ID[5:0])) ||
                 (iEXEND_ALU1_VALID && (iEXEND_ALU1_COMMIT_TAG==ENTRY_ID[5:0])) ||
                 (iEXEND_ALU2_VALID && (iEXEND_ALU2_COMMIT_TAG==ENTRY_ID[5:0])) ||
                 (iEXEND_ALU3_VALID && (iEXEND_ALU3_COMMIT_TAG==ENTRY_ID[5:0]));

    // Interface consistency
    assert property (oINFO_VALID == ((b_state==2'h1) || (b_state==2'h2)));
    assert property (oINFO_EX_END == (b_state==2'h2));
    assert property (oINFO_FREE == (iRESTART_VALID && ((b_state==2'h1)||(b_state==2'h2))));
    assert property (b_state != 2'h3);

    // Accept slot0
    assert property (cond0 |-> ##1 (oINFO_VALID && !oINFO_EX_END &&
                                    oINFO_PC == $past(iREGIST_PC) &&
                                    oINFO_MAKE_FLAGS_VALID == $past(iREGIST_0_MAKE_FLAGS) &&
                                    oINFO_WRITEBACK_VALID == $past(iREGIST_0_WRITEBACK) &&
                                    oINFO_FLAGS_PREG_POINTER == $past(iREGIST_0_FLAGS_PREG_POINTER) &&
                                    oINFO_DEST_PREG_POINTER == $past(iREGIST_0_DEST_PREG_POINTER) &&
                                    oINFO_DEST_LREG_POINTER == $past(iREGIST_0_DEST_LREG_POINTER) &&
                                    oINFO_DEST_SYSREG == $past(iREGIST_0_DEST_SYSREG) &&
                                    oINFO_EX_BRANCH == $past(iREGIST_0_EX_BRANCH)));

    // Accept slot1 only when slot0 not taken
    assert property ((!cond0 && cond1) |-> ##1 (oINFO_VALID && !oINFO_EX_END &&
                                    oINFO_PC == ($past(iREGIST_PC) + 32'h4) &&
                                    oINFO_MAKE_FLAGS_VALID == $past(iREGIST_1_MAKE_FLAGS) &&
                                    oINFO_WRITEBACK_VALID == $past(iREGIST_1_WRITEBACK) &&
                                    oINFO_FLAGS_PREG_POINTER == $past(iREGIST_1_FLAGS_PREG_POINTER) &&
                                    oINFO_DEST_PREG_POINTER == $past(iREGIST_1_DEST_PREG_POINTER) &&
                                    oINFO_DEST_LREG_POINTER == $past(iREGIST_1_DEST_LREG_POINTER) &&
                                    oINFO_DEST_SYSREG == $past(iREGIST_1_DEST_SYSREG) &&
                                    oINFO_EX_BRANCH == $past(iREGIST_1_EX_BRANCH)));

    // Arbitration: both valid -> slot0 wins
    assert property ((cond0 && cond1) |-> ##1 (oINFO_PC == $past(iREGIST_PC) &&
                                               oINFO_DEST_PREG_POINTER == $past(iREGIST_0_DEST_PREG_POINTER)));

    // Lock blocks accept
    assert property (iLOCK && (wish0 || wish1) |-> ##1 !oINFO_VALID);

    // Stay in state1 until ex_hit or restart
    assert property ((b_state==2'h1 && !ex_hit && !iRESTART_VALID) |-> ##1 (b_state==2'h1 && oINFO_VALID && !oINFO_EX_END));

    // Progress to state2 on ex_end tag hit
    assert property ((b_state==2'h1 && ex_hit) |-> ##1 (b_state==2'h2 && oINFO_EX_END));

    // Hold in state2 until commit or restart
    assert property ((b_state==2'h2 && !iCOMMIT_VALID && !iRESTART_VALID) |-> ##1 (b_state==2'h2 && oINFO_EX_END));

    // Commit advances to idle and clears defined fields
    assert property ((b_state==2'h2 && iCOMMIT_VALID) |-> ##1 (!oINFO_VALID && !oINFO_EX_END &&
                                                               b_state==2'h0 &&
                                                               b_make_flags_validl==1'b0 &&
                                                               b_writeback==1'b0 &&
                                                               b_flags_preg_pointer==4'h0 &&
                                                               b_destination_regname==6'h00 &&
                                                               b_logic_destination==5'h00 &&
                                                               b_dest_sysreg==1'b0));

    // Restart frees entry and fully clears fields next cycle
    assert property (iRESTART_VALID && ((b_state==2'h1)||(b_state==2'h2)) |-> (oINFO_FREE) ##1
                     (b_state==2'h0 &&
                      b_pc==32'h0 &&
                      b_make_flags_validl==1'b0 &&
                      b_writeback==1'b0 &&
                      b_flags_preg_pointer==4'h0 &&
                      b_destination_regname==6'h00 &&
                      b_logic_destination==5'h00 &&
                      b_dest_sysreg==1'b0 &&
                      b_ex_branch==1'b0));

    // Info signals stable while busy unless commit/restart
    assert property (((b_state==2'h1)||(b_state==2'h2)) && !iRESTART_VALID && !(b_state==2'h2 && iCOMMIT_VALID)
                     |-> ##1 ($stable(b_pc) && $stable(b_make_flags_validl) && $stable(b_writeback) &&
                              $stable(b_flags_preg_pointer) && $stable(b_destination_regname) &&
                              $stable(b_logic_destination) && $stable(b_dest_sysreg) && $stable(b_ex_branch)));

    // Edge-cause checks
    assert property ($rose(oINFO_VALID) |-> $past((b_state==2'h0) && !iLOCK &&
                       ((iREGIST_0_VALID && (ENTRY_ID==iREGIST_POINTER)) ||
                        (iREGIST_1_VALID && (ENTRY_ID==(iREGIST_POINTER + 6'h1))))));
    assert property ($rose(oINFO_EX_END) |-> $past(b_state==2'h1 && ex_hit));
    assert property (oINFO_EX_END |-> oINFO_VALID);

    // Coverage
    cover property ((b_state==2'h0) && !iLOCK && (iREGIST_0_VALID && ENTRY_ID==iREGIST_POINTER)
                    ##1 (b_state==2'h1)
                    ##[1:8] (iEXEND_ALU0_VALID && iEXEND_ALU0_COMMIT_TAG==ENTRY_ID)
                    ##1 (b_state==2'h2 && oINFO_EX_END)
                    ##1 (iCOMMIT_VALID) ##1 (b_state==2'h0));

    cover property ((b_state==2'h0) && !iLOCK && !iREGIST_0_VALID &&
                    (iREGIST_1_VALID && ENTRY_ID==(iREGIST_POINTER+6'h1))
                    ##1 (b_state==2'h1) ##[1:8] (iRESTART_VALID && oINFO_FREE) ##1 (b_state==2'h0));

    cover property ((b_state==2'h0) && !iLOCK &&
                    (iREGIST_0_VALID && ENTRY_ID==iREGIST_POINTER) &&
                    (iREGIST_1_VALID && ENTRY_ID==(iREGIST_POINTER+6'h1))
                    ##1 (oINFO_PC==$past(iREGIST_PC)));

    cover property ((b_state==2'h0) && iLOCK &&
                    ((iREGIST_0_VALID && ENTRY_ID==iREGIST_POINTER) ||
                     (iREGIST_1_VALID && ENTRY_ID==(iREGIST_POINTER+6'h1)))
                    ##1 !oINFO_VALID);
`endif
`endif