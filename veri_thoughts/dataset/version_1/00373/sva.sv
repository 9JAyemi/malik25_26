// SVA for sky130_fd_sc_ms__o2bb2a
module sky130_fd_sc_ms__o2bb2a_sva (sky130_fd_sc_ms__o2bb2a dut);

  // Sample on any relevant change
  default clocking cb @(dut.A1_N or dut.A2_N or dut.B1 or dut.B2 or dut.X); endclocking

  // Functional correctness when inputs are known: X = (~A1_N | ~A2_N) & (B1 | B2)
  property p_func_known;
    !$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2})
      |->
    (dut.X === (((~dut.A1_N)|(~dut.A2_N)) & (dut.B1|dut.B2)));
  endproperty
  assert property(p_func_known);

  // X can be unknown only if some input is unknown
  assert property ($isunknown(dut.X) |-> $isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}));

  // Structural consistency with internal nets (if visible to the tool)
  assert property (!$isunknown({dut.A1_N,dut.A2_N}) |-> (dut.nand0_out   === ~(dut.A2_N & dut.A1_N)));
  assert property (!$isunknown({dut.B1,dut.B2})     |-> (dut.or0_out     === (dut.B2 | dut.B1)));
  assert property (!$isunknown({dut.nand0_out,dut.or0_out}) |-> (dut.and0_out_X === (dut.nand0_out & dut.or0_out)));
  assert property (dut.X === dut.and0_out_X);

  // Useful implications (corner checks)
  assert property ((!$isunknown({dut.B1,dut.B2}) && (dut.B1==1'b0 && dut.B2==1'b0)) |-> (dut.X==1'b0));
  assert property ((!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) &&
                    ((dut.B1|dut.B2)==1'b1) && ((dut.A1_N & dut.A2_N)==1'b0))       |-> (dut.X==1'b1));

  // Simple transition coverage on X
  cover property ((dut.X==1'b0) ##1 (dut.X==1'b1));
  cover property ((dut.X==1'b1) ##1 (dut.X==1'b0));

  // Exhaustive input-state coverage (all 16 input combinations with known inputs)
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==0 && dut.A2_N==0 && dut.B1==0 && dut.B2==0));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==0 && dut.A2_N==0 && dut.B1==0 && dut.B2==1));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==0 && dut.A2_N==0 && dut.B1==1 && dut.B2==0));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==0 && dut.A2_N==0 && dut.B1==1 && dut.B2==1));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==0 && dut.A2_N==1 && dut.B1==0 && dut.B2==0));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==0 && dut.A2_N==1 && dut.B1==0 && dut.B2==1));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==0 && dut.A2_N==1 && dut.B1==1 && dut.B2==0));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==0 && dut.A2_N==1 && dut.B1==1 && dut.B2==1));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==1 && dut.A2_N==0 && dut.B1==0 && dut.B2==0));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==1 && dut.A2_N==0 && dut.B1==0 && dut.B2==1));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==1 && dut.A2_N==0 && dut.B1==1 && dut.B2==0));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==1 && dut.A2_N==0 && dut.B1==1 && dut.B2==1));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==1 && dut.A2_N==1 && dut.B1==0 && dut.B2==0));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==1 && dut.A2_N==1 && dut.B1==0 && dut.B2==1));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==1 && dut.A2_N==1 && dut.B1==1 && dut.B2==0));
  cover property (!$isunknown({dut.A1_N,dut.A2_N,dut.B1,dut.B2}) && (dut.A1_N==1 && dut.A2_N==1 && dut.B1==1 && dut.B2==1));

endmodule

// Bind into DUT
bind sky130_fd_sc_ms__o2bb2a sky130_fd_sc_ms__o2bb2a_sva sva_inst(.dut());