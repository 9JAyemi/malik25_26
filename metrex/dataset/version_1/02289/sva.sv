// SVA for scan_chain_interface
// Bindable, concise, full functional equivalence checks + basic coverage

module scan_chain_interface_sva (
  input ctu_tst_pre_grst_l,
  input arst_l,
  input global_shift_enable,
  input ctu_tst_scan_disable,
  input ctu_tst_scanmode,
  input ctu_tst_macrotest,
  input ctu_tst_short_chain,
  input long_chain_so_0,
  input short_chain_so_0,
  input long_chain_so_1,
  input short_chain_so_1,
  input long_chain_so_2,
  input short_chain_so_2,
  input mux_drive_disable,
  input mem_write_disable,
  input sehold,
  input se,
  input testmode_l,
  input mem_bypass,
  input so_0,
  input so_1,
  input so_2
);

  // Combinational assertion sampling
  default clocking cb @(*); endclocking

  // Expected select expression (short_chain_select)
  logic scs_exp;
  assign scs_exp = ctu_tst_short_chain
                 & ctu_tst_scanmode
                 & ~(ctu_tst_scan_disable & global_shift_enable);

  // X-prop gating vectors
  logic [12:0] in_vec;
  logic [8:0]  out_vec;
  assign in_vec  = {
    ctu_tst_pre_grst_l, arst_l, global_shift_enable,
    ctu_tst_scan_disable, ctu_tst_scanmode, ctu_tst_macrotest, ctu_tst_short_chain,
    long_chain_so_0, short_chain_so_0,
    long_chain_so_1, short_chain_so_1,
    long_chain_so_2, short_chain_so_2
  };
  assign out_vec = {
    se, testmode_l, mem_bypass, sehold,
    mux_drive_disable, mem_write_disable,
    so_0, so_1, so_2
  };

  // Functional equivalence assertions
  assert property (se == global_shift_enable);

  assert property (testmode_l == ~ctu_tst_scanmode);

  assert property (mem_bypass == (~ctu_tst_macrotest & ctu_tst_scanmode));

  assert property (so_0 == (scs_exp ? short_chain_so_0 : long_chain_so_0));
  assert property (so_1 == (scs_exp ? short_chain_so_1 : long_chain_so_1));
  assert property (so_2 == (scs_exp ? short_chain_so_2 : long_chain_so_2));

  assert property (mux_drive_disable == (~ctu_tst_pre_grst_l | scs_exp | se));

  assert property (mem_write_disable == (~ctu_tst_pre_grst_l | se));

  assert property (sehold == (ctu_tst_macrotest & ~se));

  // Outputs must be known when all inputs are known
  assert property ((!$isunknown(in_vec)) |-> (!$isunknown(out_vec)));

  // Minimal but meaningful coverage
  cover property (scs_exp);
  cover property (!scs_exp);

  cover property (se);
  cover property (!se);

  cover property (~ctu_tst_pre_grst_l);

  cover property (ctu_tst_macrotest && !se);

  cover property (ctu_tst_scanmode);
  cover property (!ctu_tst_scanmode);

endmodule

// Bind into DUT
bind scan_chain_interface scan_chain_interface_sva sva_scan_chain_interface (.*);