// SVA bind file for pcie_7x_v1_3_rxeq_scan
// Focus: FSM correctness, handshakes, counters, pipelining, outputs mapping, and coverage.

bind pcie_7x_v1_3_rxeq_scan pcie_7x_v1_3_rxeq_scan_sva();

module pcie_7x_v1_3_rxeq_scan_sva;

  // Local aliases (refer to bound instance signals directly)
  // Clock/reset
  wire clk   = RXEQSCAN_CLK;
  wire rst_n = RXEQSCAN_RST_N;

  // FSM encodings
  localparam [2:0] FSM_IDLE            = 3'b001;
  localparam [2:0] FSM_PRESET          = 3'b010;
  localparam [2:0] FSM_NEW_TXCOEFF_REQ = 3'b100;

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // --------------------------
  // Reset dominance and encoding
  // --------------------------
  // Synchronous reset values
  assert property (cb, !rst_n |-> 
      fsm==FSM_IDLE &&
      preset_done==0 && new_txcoeff==18'd0 && new_txcoeff_done==0 &&
      lffs_sel==0 && lffs_sel_cnt==2'd0 && adapt_done==0 && adapt_done_cnt==3'd0 &&
      preset_reg1==0 && preset_valid_reg1==0 && txpreset_reg1==0 &&
      txcoeff_reg1==0 && new_txcoeff_req_reg1==0 && fs_reg1==0 && lf_reg1==0 &&
      preset_reg2==0 && preset_valid_reg2==0 && txpreset_reg2==0 &&
      txcoeff_reg2==0 && new_txcoeff_req_reg2==0 && fs_reg2==0 && lf_reg2==0
  );

  // FSM only in legal encodings when out of reset
  assert property (cb, disable iff (!rst_n)
      fsm inside {FSM_IDLE, FSM_PRESET, FSM_NEW_TXCOEFF_REQ}
  );

  // --------------------------
  // Two-stage input pipeline checks
  // --------------------------
  assert property (cb, disable iff (!rst_n) preset_reg1          == $past(RXEQSCAN_PRESET));
  assert property (cb, disable iff (!rst_n) preset_valid_reg1    == $past(RXEQSCAN_PRESET_VALID));
  assert property (cb, disable iff (!rst_n) txpreset_reg1        == $past(RXEQSCAN_TXPRESET));
  assert property (cb, disable iff (!rst_n) txcoeff_reg1         == $past(RXEQSCAN_TXCOEFF));
  assert property (cb, disable iff (!rst_n) new_txcoeff_req_reg1 == $past(RXEQSCAN_NEW_TXCOEFF_REQ));
  assert property (cb, disable iff (!rst_n) fs_reg1              == $past(RXEQSCAN_FS));
  assert property (cb, disable iff (!rst_n) lf_reg1              == $past(RXEQSCAN_LF));

  assert property (cb, disable iff (!rst_n) preset_reg2          == $past(preset_reg1));
  assert property (cb, disable iff (!rst_n) preset_valid_reg2    == $past(preset_valid_reg1));
  assert property (cb, disable iff (!rst_n) txpreset_reg2        == $past(txpreset_reg1));
  assert property (cb, disable iff (!rst_n) txcoeff_reg2         == $past(txcoeff_reg1));
  assert property (cb, disable iff (!rst_n) new_txcoeff_req_reg2 == $past(new_txcoeff_req_reg1));
  assert property (cb, disable iff (!rst_n) fs_reg2              == $past(fs_reg1));
  assert property (cb, disable iff (!rst_n) lf_reg2              == $past(lf_reg1));

  // --------------------------
  // Output mapping checks
  // --------------------------
  assert property (cb, disable iff (!rst_n) RXEQSCAN_PRESET_DONE      == preset_done);
  assert property (cb, disable iff (!rst_n) RXEQSCAN_NEW_TXCOEFF      == new_txcoeff);
  assert property (cb, disable iff (!rst_n) RXEQSCAN_NEW_TXCOEFF_DONE == new_txcoeff_done);
  assert property (cb, disable iff (!rst_n) RXEQSCAN_LFFS_SEL         == lffs_sel);
  assert property (cb, disable iff (!rst_n) RXEQSCAN_ADAPT_DONE       == adapt_done);

  // --------------------------
  // IDLE behavior
  // --------------------------
  // Priority: PRESET dominates NEW_TXCOEFF_REQ when both are seen in IDLE
  assert property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && $past(preset_valid_reg2) && $past(new_txcoeff_req_reg2)
    |=> fsm==FSM_PRESET && preset_done==1 && new_txcoeff_done==0 && lffs_sel==0 &&
        $stable(new_txcoeff) && $stable(lffs_sel_cnt) && $stable(adapt_done_cnt) && adapt_done==0
  );

  // IDLE -> PRESET transition
  assert property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && $past(preset_valid_reg2)
    |=> fsm==FSM_PRESET && preset_done==1 && new_txcoeff_done==0 && lffs_sel==0 &&
        $stable(new_txcoeff) && $stable(lffs_sel_cnt) && $stable(adapt_done_cnt) && adapt_done==0
  );

  // IDLE -> NEW_TXCOEFF_REQ transition
  assert property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && $past(new_txcoeff_req_reg2) && !$past(preset_valid_reg2)
    |=> fsm==FSM_NEW_TXCOEFF_REQ && preset_done==0 && new_txcoeff_done==1 &&
        new_txcoeff==$past(txcoeff_reg2) &&
        lffs_sel_cnt==$past(lffs_sel_cnt)+1 &&
        lffs_sel==($past(lffs_sel_cnt)==2'd1) &&
        adapt_done_cnt==$past(adapt_done_cnt)+1 &&
        adapt_done==($past(adapt_done_cnt)==3'd1)
  );

  // IDLE hold (no requests)
  assert property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && !$past(preset_valid_reg2) && !$past(new_txcoeff_req_reg2)
    |=> fsm==FSM_IDLE && preset_done==0 && new_txcoeff_done==0 && lffs_sel==0 &&
        $stable(new_txcoeff) && $stable(lffs_sel_cnt) && $stable(adapt_done_cnt) && adapt_done==0
  );

  // --------------------------
  // PRESET behavior
  // --------------------------
  // Stay in PRESET while preset_valid_reg2 is high
  assert property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_PRESET && $past(preset_valid_reg2)
    |=> fsm==FSM_PRESET && preset_done==1 && new_txcoeff_done==0 && lffs_sel==0 &&
        $stable(new_txcoeff) && $stable(lffs_sel_cnt) && $stable(adapt_done_cnt) && adapt_done==0
  );

  // Exit PRESET when preset_valid_reg2 deasserts
  assert property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_PRESET && !$past(preset_valid_reg2)
    |=> fsm==FSM_IDLE && preset_done==1 && new_txcoeff_done==0 && lffs_sel==0 &&
        $stable(new_txcoeff) && $stable(lffs_sel_cnt) && $stable(adapt_done_cnt) && adapt_done==0
  );

  // --------------------------
  // NEW_TXCOEFF_REQ behavior
  // --------------------------
  // Stay in NEW while new_txcoeff_req_reg2 is high (all hold)
  assert property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_NEW_TXCOEFF_REQ && $past(new_txcoeff_req_reg2)
    |=> fsm==FSM_NEW_TXCOEFF_REQ && preset_done==0 && new_txcoeff_done==1 &&
        $stable(new_txcoeff) && $stable(lffs_sel) && $stable(lffs_sel_cnt) &&
        $stable(adapt_done) && $stable(adapt_done_cnt)
  );

  // Exit NEW when new_txcoeff_req_reg2 deasserts
  assert property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_NEW_TXCOEFF_REQ && !$past(new_txcoeff_req_reg2)
    |=> fsm==FSM_IDLE && preset_done==0 && new_txcoeff_done==1 &&
        $stable(new_txcoeff) && $stable(lffs_sel) && $stable(lffs_sel_cnt) &&
        $stable(adapt_done) && $stable(adapt_done_cnt)
  );

  // --------------------------
  // Counter and data update locality
  // --------------------------
  // lffs_sel_cnt only changes on IDLE->NEW transition (and increments by 1)
  assert property (cb, disable iff (!rst_n)
    (lffs_sel_cnt != $past(lffs_sel_cnt)) |->
      $past(fsm)==FSM_IDLE && $past(new_txcoeff_req_reg2) && !$past(preset_valid_reg2) &&
      lffs_sel_cnt==$past(lffs_sel_cnt)+1
  );

  // adapt_done_cnt only changes on IDLE->NEW transition (and increments by 1)
  assert property (cb, disable iff (!rst_n)
    (adapt_done_cnt != $past(adapt_done_cnt)) |->
      $past(fsm)==FSM_IDLE && $past(new_txcoeff_req_reg2) && !$past(preset_valid_reg2) &&
      adapt_done_cnt==$past(adapt_done_cnt)+1
  );

  // new_txcoeff only changes on IDLE->NEW transition, to txcoeff_reg2
  assert property (cb, disable iff (!rst_n)
    (new_txcoeff != $past(new_txcoeff)) |->
      $past(fsm)==FSM_IDLE && $past(new_txcoeff_req_reg2) && !$past(preset_valid_reg2) &&
      new_txcoeff==$past(txcoeff_reg2)
  );

  // --------------------------
  // Coverage
  // --------------------------
  // Visit each state
  cover property (cb, disable iff (!rst_n) fsm==FSM_IDLE);
  cover property (cb, disable iff (!rst_n) fsm==FSM_PRESET);
  cover property (cb, disable iff (!rst_n) fsm==FSM_NEW_TXCOEFF_REQ);

  // Exercise both transitions
  cover property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && $past(preset_valid_reg2) ##1 fsm==FSM_PRESET ##1
    !$past(preset_valid_reg2) ##1 fsm==FSM_IDLE
  );

  cover property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && $past(new_txcoeff_req_reg2) && !$past(preset_valid_reg2)
    ##1 fsm==FSM_NEW_TXCOEFF_REQ ##1 !$past(new_txcoeff_req_reg2) ##1 fsm==FSM_IDLE
  );

  // Priority scenario: both asserted in IDLE picks PRESET
  cover property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && $past(preset_valid_reg2) && $past(new_txcoeff_req_reg2) ##1 fsm==FSM_PRESET
  );

  // Observe lffs_sel/adapt_done assertion when count==1 on a NEW request
  cover property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && $past(new_txcoeff_req_reg2) && $past(lffs_sel_cnt)==2'd1
    ##1 lffs_sel==1
  );
  cover property (cb, disable iff (!rst_n)
    $past(fsm)==FSM_IDLE && $past(new_txcoeff_req_reg2) && $past(adapt_done_cnt)==3'd1
    ##1 adapt_done==1
  );

endmodule