// SVA for add_sub. Bind this module to the DUT: bind add_sub add_sub_sva sva();
module add_sub_sva (add_sub dut);

  // Stage1 registers follow inputs (after delta), carry/borrow in are 0
  property p_stage1_regs_follow;
    @(dut.A or dut.B or dut.CTRL)
      1'b1 |-> ##0 (dut.A_reg == dut.A &&
                    dut.B_reg == dut.B &&
                    dut.CTRL_reg == dut.CTRL &&
                    dut.CARRY_IN_reg == 1'b0 &&
                    dut.BORROW_IN_reg == 1'b0);
  endproperty
  assert property (p_stage1_regs_follow);

  // Stage2 add path: arithmetic and BORROW_OUT formula
  property p_stage2_add;
    @(dut.A_reg or dut.B_reg or dut.CTRL_reg or dut.CARRY_IN_reg or dut.BORROW_IN_reg)
      (dut.CTRL_reg == 1'b0) |-> ##0 (
        {dut.CARRY_OUT, dut.SUM_DIFF_reg} == ({1'b0,dut.A_reg} + {1'b0,dut.B_reg} + dut.CARRY_IN_reg) &&
        dut.BORROW_OUT == ((dut.A_reg < dut.B_reg) || ((dut.A_reg == dut.B_reg) && (dut.CARRY_IN_reg == 1'b1)))
      );
  endproperty
  assert property (p_stage2_add);

  // Stage2 sub path: arithmetic and CARRY_OUT formula
  property p_stage2_sub;
    @(dut.A_reg or dut.B_reg or dut.CTRL_reg or dut.CARRY_IN_reg or dut.BORROW_IN_reg)
      (dut.CTRL_reg == 1'b1) |-> ##0 (
        {dut.BORROW_OUT, dut.SUM_DIFF_reg} == ({1'b0,dut.A_reg} - {1'b0,dut.B_reg} - dut.BORROW_IN_reg) &&
        dut.CARRY_OUT == ((dut.A_reg >= dut.B_reg) && ((dut.A_reg != dut.B_reg) || (dut.BORROW_IN_reg == 1'b1)))
      );
  endproperty
  assert property (p_stage2_sub);

  // Stage3 pass-through
  property p_stage3_passthrough;
    @(dut.SUM_DIFF_reg) 1'b1 |-> ##0 (dut.SUM_DIFF == dut.SUM_DIFF_reg);
  endproperty
  assert property (p_stage3_passthrough);

  // Top-level output mux correctness
  property p_top_mux;
    @(dut.CTRL or dut.CARRY_OUT or dut.BORROW_OUT or dut.CARRY_OUT_BORROW_OUT)
      1'b1 |-> ##0 (
        ((dut.CTRL==1'b0) && (dut.CARRY_OUT_BORROW_OUT == dut.CARRY_OUT)) ||
        ((dut.CTRL==1'b1) && (dut.CARRY_OUT_BORROW_OUT == dut.BORROW_OUT))
      );
  endproperty
  assert property (p_top_mux);

  // End-to-end functional checks from inputs to outputs (2 delta steps through the 3 "stages")
  property p_e2e_add;
    @(dut.A or dut.B or dut.CTRL)
      (dut.CTRL==1'b0) |-> ##2 (
        dut.SUM_DIFF == (dut.A + dut.B) &&
        dut.CARRY_OUT_BORROW_OUT == ({1'b0,dut.A} + {1'b0,dut.B})[16]
      );
  endproperty
  assert property (p_e2e_add);

  property p_e2e_sub;
    @(dut.A or dut.B or dut.CTRL)
      (dut.CTRL==1'b1) |-> ##2 (
        dut.SUM_DIFF == (dut.A - dut.B) &&
        dut.CARRY_OUT_BORROW_OUT == ({1'b0,dut.A} - {1'b0,dut.B})[16]
      );
  endproperty
  assert property (p_e2e_sub);

  // Knownness: if inputs known, outputs known after pipeline settles
  property p_no_x;
    @ (dut.A or dut.B or dut.CTRL)
      (!$isunknown({dut.A,dut.B,dut.CTRL})) |-> ##2 (!$isunknown({dut.SUM_DIFF,dut.CARRY_OUT_BORROW_OUT}));
  endproperty
  assert property (p_no_x);

  // Coverage: exercise both modes and corner carry/borrow conditions
  cover property (@(posedge dut.CTRL) 1'b1);   // add->sub
  cover property (@(negedge dut.CTRL) 1'b1);   // sub->add

  cover property (@(dut.A or dut.B or dut.CTRL)
                    (dut.CTRL==1'b0) ##2 (({1'b0,dut.A}+{1'b0,dut.B})[16]==1'b1)); // add carry
  cover property (@(dut.A or dut.B or dut.CTRL)
                    (dut.CTRL==1'b1) ##2 (({1'b0,dut.A}-{1'b0,dut.B})[16]==1'b1)); // sub borrow
  cover property (@(dut.A or dut.B or dut.CTRL)
                    (dut.CTRL==1'b1) ##2 (dut.A==dut.B && dut.SUM_DIFF==16'h0000)); // zero diff
endmodule