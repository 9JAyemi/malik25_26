// SVA for minimac2_sync and minimac2_psync
// Focus: CDC pulse synchronizer correctness and count pipe integrity.
// Bind these modules in your testbench or include alongside the DUT.

///////////////////////////////////////////////////////////////
// Assertions bound into minimac2_psync (internal-signal aware)
///////////////////////////////////////////////////////////////
module minimac2_psync_sva;
  // We are bound into minimac2_psync scope; can see clk1, clk2, i, o, pulse, intermediate, sync_reg
  int c1, c2;
  always @(posedge clk1) c1 <= c1 + 1;
  always @(posedge clk2) c2 <= c2 + 1;

  // o must be a 2-cycle pulse (exactly) in clk2 domain
  assert property (@(posedge clk2) (c2>1 && $rose(o)) |-> o[*2] ##1 !o);

  // o cannot rise from a high state (no double-rise)
  assert property (@(posedge clk2) (c2>0 && $rose(o)) |-> !$past(o));

  // Shape relation to internal pipeline: o equals prior sync_reg[1]
  assert property (@(posedge clk2) (c2>0) |-> (o == $past(sync_reg[1])));

  // Causality: o can only rise if intermediate was set previously
  assert property (@(posedge clk2) (c2>0 && $rose(o)) |-> $past(intermediate));

  // If clk2 samples pulse, a dest pulse must appear 2 cycles later
  assert property (@(posedge clk2) (c2>0 && pulse) |-> ##2 $rose(o));

  // When acknowledging (sync_reg[1]==1) and no new pulse, intermediate must clear
  assert property (@(posedge clk2) (c2>0 && sync_reg[1] && !pulse) |=> !intermediate);

  // Basic coverage: source edge leads to a dest pulse within a small window
  cover property (@(posedge clk1) $rose(i) ##0 @(posedge clk2) ##[1:8] $rose(o));
  // Cover the 2-cycle pulse shape
  cover property (@(posedge clk2) $rose(o) ##1 o ##1 !o);
endmodule

bind minimac2_psync minimac2_psync_sva psync_sva_i();

///////////////////////////////////////////////////////////////
// Assertions bound into minimac2_sync (top-level integrity)
///////////////////////////////////////////////////////////////
module minimac2_sync_sva;
  // Bound into minimac2_sync; can see all its ports/regs
  int sys_c, rx_c, tx_c;
  always @(posedge sys_clk)    sys_c <= sys_c + 1;
  always @(posedge phy_rx_clk) rx_c  <= rx_c  + 1;
  always @(posedge phy_tx_clk) tx_c  <= tx_c  + 1;

  // Count pipelines: 2-cycle sampling pipes
  assert property (@(posedge sys_clk) (sys_c>1) |-> (sys_rx_count_0 == $past(phy_rx_count_0,2)));
  assert property (@(posedge sys_clk) (sys_c>1) |-> (sys_rx_count_1 == $past(phy_rx_count_1,2)));
  assert property (@(posedge phy_tx_clk) (tx_c>1) |-> (phy_tx_count    == $past(sys_tx_count,2)));

  // No X/Z on primary outputs once clocks have started
  assert property (@(posedge sys_clk)    (sys_c>1) |-> !$isunknown({sys_rx_done,sys_rx_count_0,sys_rx_count_1,sys_tx_done}));
  assert property (@(posedge phy_rx_clk) (rx_c>1)  |-> !$isunknown({phy_rx_ready}));
  assert property (@(posedge phy_tx_clk) (tx_c>1)  |-> !$isunknown({phy_tx_start,phy_tx_count}));

  // Functional coverage: exercise each CDC path
  cover property (@(posedge sys_clk)    $rose(sys_rx_ready[0]));
  cover property (@(posedge sys_clk)    $rose(sys_rx_ready[1]));
  cover property (@(posedge phy_rx_clk) $rose(phy_rx_done[0]));
  cover property (@(posedge phy_rx_clk) $rose(phy_rx_done[1]));
  cover property (@(posedge sys_clk)    $rose(sys_tx_start));
  cover property (@(posedge phy_tx_clk) $rose(phy_tx_done));
endmodule

bind minimac2_sync minimac2_sync_sva top_sva_i();