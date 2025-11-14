// SVA for test_stub_scan
module test_stub_scan_sva(
  input  logic ctu_tst_pre_grst_l,
  input  logic arst_l,
  input  logic global_shift_enable,
  input  logic ctu_tst_scan_disable,
  input  logic ctu_tst_scanmode,
  input  logic ctu_tst_macrotest,
  input  logic ctu_tst_short_chain,
  input  logic long_chain_so_0,
  input  logic short_chain_so_0,
  input  logic long_chain_so_1,
  input  logic short_chain_so_1,
  input  logic long_chain_so_2,
  input  logic short_chain_so_2,
  input  logic mux_drive_disable,
  input  logic mem_write_disable,
  input  logic sehold,
  input  logic se,
  input  logic testmode_l,
  input  logic mem_bypass,
  input  logic so_0,
  input  logic so_1,
  input  logic so_2
);

  // Derived selector (using DUT outputs) and pure-input equivalent
  logic short_sel_out, short_sel_pure;

  always @* begin
    short_sel_out  = ctu_tst_short_chain & ~testmode_l & ~(ctu_tst_scan_disable & se);
    short_sel_pure = ctu_tst_short_chain & ctu_tst_scanmode & ~(ctu_tst_scan_disable & global_shift_enable);

    // Functional equivalence (deferred immediate assertions avoid delta-cycle races)
    assert #0 (se == global_shift_enable)
      else $error("se != global_shift_enable");

    assert #0 (testmode_l == ~ctu_tst_scanmode)
      else $error("testmode_l != ~ctu_tst_scanmode");

    assert #0 (short_sel_out == short_sel_pure)
      else $error("short_chain_select expression mismatch");

    assert #0 (mem_bypass == (~ctu_tst_macrotest & ~testmode_l))
      else $error("mem_bypass != (~ctu_tst_macrotest & ~testmode_l)");

    assert #0 (mem_bypass == (~ctu_tst_macrotest & ctu_tst_scanmode))
      else $error("mem_bypass != (~ctu_tst_macrotest & ctu_tst_scanmode)");

    assert #0 (sehold == (ctu_tst_macrotest & ~se))
      else $error("sehold != (ctu_tst_macrotest & ~se)");

    assert #0 (mem_write_disable == (~ctu_tst_pre_grst_l | se))
      else $error("mem_write_disable equation mismatch");

    assert #0 (mux_drive_disable == (~ctu_tst_pre_grst_l | short_sel_out | se))
      else $error("mux_drive_disable equation mismatch");

    assert #0 (so_0 == (short_sel_out ? short_chain_so_0 : long_chain_so_0))
      else $error("so_0 mux mismatch");

    assert #0 (so_1 == (short_sel_out ? short_chain_so_1 : long_chain_so_1))
      else $error("so_1 mux mismatch");

    assert #0 (so_2 == (short_sel_out ? short_chain_so_2 : long_chain_so_2))
      else $error("so_2 mux mismatch");

    // X/knownness checks (only when driving inputs are known)
    if (!$isunknown(global_shift_enable))
      assert #0 (!$isunknown(se)) else $error("se is X with known global_shift_enable");

    if (!$isunknown(ctu_tst_scanmode))
      assert #0 (!$isunknown(testmode_l)) else $error("testmode_l is X with known ctu_tst_scanmode");

    if (!$isunknown({ctu_tst_macrotest, testmode_l}))
      assert #0 (!$isunknown(mem_bypass)) else $error("mem_bypass is X with known inputs");

    if (!$isunknown({ctu_tst_macrotest, se}))
      assert #0 (!$isunknown(sehold)) else $error("sehold is X with known inputs");

    if (!$isunknown({ctu_tst_pre_grst_l, se}))
      assert #0 (!$isunknown(mem_write_disable)) else $error("mem_write_disable is X with known inputs");

    if (!$isunknown({ctu_tst_pre_grst_l, ctu_tst_short_chain, ctu_tst_scanmode, ctu_tst_scan_disable, global_shift_enable}))
      assert #0 (!$isunknown(mux_drive_disable)) else $error("mux_drive_disable is X with known inputs");

    if (!$isunknown({short_sel_pure, short_chain_so_0, long_chain_so_0}))
      assert #0 (!$isunknown(so_0)) else $error("so_0 is X with known inputs");

    if (!$isunknown({short_sel_pure, short_chain_so_1, long_chain_so_1}))
      assert #0 (!$isunknown(so_1)) else $error("so_1 is X with known inputs");

    if (!$isunknown({short_sel_pure, short_chain_so_2, long_chain_so_2}))
      assert #0 (!$isunknown(so_2)) else $error("so_2 is X with known inputs");

    // Minimal but meaningful functional coverage
    cover #0 (se == 0);
    cover #0 (se == 1);
    cover #0 (testmode_l == 0);
    cover #0 (testmode_l == 1);
    cover #0 (mem_bypass == 0);
    cover #0 (mem_bypass == 1);
    cover #0 (short_sel_out == 0);
    cover #0 (short_sel_out == 1);
    cover #0 (short_sel_out && (so_0==short_chain_so_0) && (so_1==short_chain_so_1) && (so_2==short_chain_so_2));
    cover #0 (!short_sel_out && (so_0==long_chain_so_0) && (so_1==long_chain_so_1) && (so_2==long_chain_so_2));
    cover #0 (~ctu_tst_pre_grst_l && mux_drive_disable && mem_write_disable);
    cover #0 (ctu_tst_scan_disable && se); // pin-based scan disables short chain during shift
  end
endmodule

bind test_stub_scan test_stub_scan_sva sva_test_stub_scan (.*);