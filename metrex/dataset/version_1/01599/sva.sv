// SVA for mux_2_to_1: bind without touching DUT

bind mux_2_to_1 mux_2_to_1_sva i_mux_2_to_1_sva();

module mux_2_to_1_sva (mux_2_to_1 dut);

  // Sample on DUT clock
  default clocking cb @(posedge dut.clk); endclocking

  // Guard $past usage
  bit past_valid;
  initial past_valid = 0;
  always @(posedge dut.clk) past_valid <= 1;

  // Control must be 2-state
  a_ctrl_2state: assert property (disable iff (!past_valid)
    !$isunknown(dut.S));

  // Pipeline stage captures (A/B registered)
  a_regA_cap: assert property (disable iff (!past_valid)
    !$isunknown($past(dut.A)) |-> dut.reg_A == $past(dut.A));
  a_regB_cap: assert property (disable iff (!past_valid)
    !$isunknown($past(dut.B)) |-> dut.reg_B == $past(dut.B));

  // Functional mux behavior: Y = prev(A) or prev(B) selected by current S
  a_mux_func: assert property (disable iff (!past_valid)
    (!$isunknown(dut.S) && !$isunknown($past({dut.A,dut.B})))
    |-> dut.Y == (dut.S ? $past(dut.B) : $past(dut.A)));

  // No X on Y when inputs/control are known
  a_y_known: assert property (disable iff (!past_valid)
    (!$isunknown(dut.S) && !$isunknown($past({dut.A,dut.B})))
    |-> !$isunknown(dut.Y));

  // Coverage
  c_sel0:  cover property (past_valid && dut.S==0 && !$isunknown($past(dut.A)) && dut.Y==$past(dut.A));
  c_sel1:  cover property (past_valid && dut.S==1 && !$isunknown($past(dut.B)) && dut.Y==$past(dut.B));
  c_S_01:  cover property (past_valid && $past(dut.S)==0 && dut.S==1);
  c_S_10:  cover property (past_valid && $past(dut.S)==1 && dut.S==0);
  c_Y_tog: cover property (past_valid && $changed(dut.Y));

endmodule