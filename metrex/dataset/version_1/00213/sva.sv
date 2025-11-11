// SVA for LCDCONTROL
// Bind this module to the DUT: bind LCDCONTROL LCDCONTROL_sva sva();

module LCDCONTROL_sva (LCDCONTROL dut);

  default clocking cb @(posedge dut.CLK); endclocking

  // Basic decodes and constants
  a_const_rw:     assert property (dut.LCD_RW == 1'b0);
  a_const_bl:     assert property (dut.LCD_BLON == 1'b1);
  a_decode_rs:    assert property (dut.LCD_RS == dut.cmd[8]);
  a_decode_data:  assert property (dut.LCD_DATA == dut.cmd[7:0]);
  a_en_def:       assert property (dut.LCD_EN == (dut.en_cnt != 5'h0));
  a_st_def:       assert property (dut.st == (dut.WRITE && !dut.busy));
  a_busy_def:     assert property (dut.busy == ((dut.en_cnt != 5'h0) || (dut.wait_cnt != 18'h0)));

  // Reset/delay invariants
  a_rst_dly_def:  assert property (dut.rst_dly == (dut.dly_cnt != 20'hFFFFF));
  a_dly_sat:      assert property (dut.dly_cnt == 20'hFFFFF |=> dut.dly_cnt == 20'hFFFFF);
  a_in_reset:     assert property (dut.RST |-> (dut.cmd==9'h0 && dut.en_cnt==5'h0 && dut.wait_cnt==18'h0 && dut.STATUS==1'b1));
  a_in_rst_dly:   assert property (dut.rst_dly |-> (dut.cmd==9'h0 && dut.en_cnt==5'h0 && dut.wait_cnt==18'h0 && dut.STATUS==1'b1));

  // Next-state: command capture and enable pulse
  a_cmd_load:     assert property (disable iff (dut.RST || dut.rst_dly) dut.st |=> dut.cmd == $past(dut.WRDATA));
  a_en_load:      assert property (disable iff (dut.RST || dut.rst_dly) dut.st |=> dut.en_cnt == 5'h10);
  a_en_dec:       assert property (disable iff (dut.RST || dut.rst_dly) (!dut.st && dut.en_cnt != 5'h0) |=> dut.en_cnt == $past(dut.en_cnt) - 5'h1);
  a_en_hold0:     assert property (disable iff (dut.RST || dut.rst_dly) (!dut.st && dut.en_cnt == 5'h0) |=> dut.en_cnt == 5'h0);
  a_en_len:       assert property (disable iff (dut.RST || dut.rst_dly) dut.st |=> dut.LCD_EN[*16] ##1 !dut.LCD_EN);

  // Wait counter behavior
  a_wait_load:    assert property (disable iff (dut.RST || dut.rst_dly) (dut.en_cnt == 5'h1) |=> dut.wait_cnt == 18'h3FFFF);
  a_wait_dec:     assert property (disable iff (dut.RST || dut.rst_dly) (dut.wait_cnt != 18'h0 && dut.en_cnt != 5'h1) |=> dut.wait_cnt == $past(dut.wait_cnt) - 18'h1);
  a_wait_hold0:   assert property (disable iff (dut.RST || dut.rst_dly) (dut.wait_cnt == 18'h0 && dut.en_cnt != 5'h1) |=> dut.wait_cnt == 18'h0);

  // Status and gating
  a_status_def:   assert property (disable iff (dut.RST || dut.rst_dly) dut.STATUS == (dut.st || dut.busy));
  a_no_st_while_busy: assert property (disable iff (dut.RST || dut.rst_dly) dut.busy |-> !dut.st);

  // Stability while busy (after the load edge)
  a_cmd_stable_busy: assert property (disable iff (dut.RST || dut.rst_dly) (dut.busy && !$past(dut.st)) |-> $stable(dut.cmd));

  // No X/Z on key outputs
  a_no_x:         assert property (!$isunknown({dut.STATUS,dut.LCD_EN,dut.LCD_RS,dut.LCD_RW,dut.LCD_BLON,dut.LCD_DATA})));

  // Coverage
  c_basic_txn:    cover  property (disable iff (dut.RST) (!dut.rst_dly ##1 dut.st ##[1:$] !dut.busy));
  c_b2b_txn:      cover  property (disable iff (dut.RST) (!dut.rst_dly ##1 dut.st ##[1:$] !dut.busy ##1 dut.st));

endmodule