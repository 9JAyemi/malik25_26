// Bind these assertions into the DUT
bind hls_macc_HLS_MACC_PERIPH_BUS_s_axi hls_macc_HLS_MACC_PERIPH_BUS_s_axi_sva();

module hls_macc_HLS_MACC_PERIPH_BUS_s_axi_sva;

  default clocking cb @(posedge ACLK); endclocking
  default disable iff (ARESET);

  // ---------------- AXI4-Lite core protocol ----------------

  // Ready/valid/state relationships and persistence
  assert property (AWREADY == (wstate == WRIDLE));
  assert property (WREADY  == (wstate == WRDATA));
  assert property (BVALID  == (wstate == WRRESP));
  assert property (ARREADY == (rstate == RDIDLE));
  assert property (RVALID  == (rstate == RDDATA));

  assert property (!(AWREADY && WREADY));  // mutual exclusive

  assert property (BVALID && !BREADY |=> BVALID);
  assert property (RVALID && !RREADY |=> RVALID);

  // State transitions (when enabled)
  assert property (ACLK_EN && (wstate==WRIDLE) &&  AWVALID |=> wstate==WRDATA);
  assert property (ACLK_EN && (wstate==WRIDLE) && !AWVALID |=> wstate==WRIDLE);
  assert property (ACLK_EN && (wstate==WRDATA) &&  WVALID |=> wstate==WRRESP);
  assert property (ACLK_EN && (wstate==WRDATA) && !WVALID |=> wstate==WRDATA);
  assert property (ACLK_EN && (wstate==WRRESP) &&  BREADY |=> wstate==WRIDLE);
  assert property (ACLK_EN && (wstate==WRRESP) && !BREADY |=> wstate==WRRESP);

  assert property (ACLK_EN && (rstate==RDIDLE) &&  ARVALID |=> rstate==RDDATA);
  assert property (ACLK_EN && (rstate==RDIDLE) && !ARVALID |=> rstate==RDIDLE);
  assert property (ACLK_EN && (rstate==RDDATA) &&  (RREADY && RVALID) |=> rstate==RDIDLE);
  assert property (ACLK_EN && (rstate==RDDATA) && !(RREADY && RVALID) |=> rstate==RDDATA);

  // Address/data stability till handshake (master well-formedness)
  assert property (AWVALID && !AWREADY |=> $stable(AWADDR));
  assert property (WVALID  && !WREADY  |=> $stable({WSTRB,WDATA}));
  assert property (ARVALID && !ARREADY |=> $stable(ARADDR));

  // Handshake capture and ordering
  assert property (ACLK_EN && aw_hs |=> waddr == $past(AWADDR[ADDR_BITS-1:0]));
  assert property (BVALID |-> $past(ACLK_EN && w_hs));       // response only after W handshake
  assert property (ACLK_EN && ar_hs |=> RVALID);             // 1-cycle latency read

  // RDATA holds stable until RREADY
  assert property (RVALID && !RREADY |=> $stable(RDATA));

  // ---------------- Read data decode checks ----------------

  // AP_CTRL: bits [0]=start, [1]=done, [2]=idle, [3]=ready, [7]=auto, others zero
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_AP_CTRL) |=> RVALID
                   && RDATA[0]  == $past(int_ap_start)
                   && RDATA[1]  == $past(int_ap_done)
                   && RDATA[2]  == $past(int_ap_idle)
                   && RDATA[3]  == $past(int_ap_ready)
                   && RDATA[7]  == $past(int_auto_restart)
                   && RDATA[6:4]== 3'b0 && RDATA[31:8]==24'h0);

  // GIE: bit0
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_GIE) |=> RVALID
                   && RDATA[0]==$past(int_gie) && RDATA[31:1]==31'h0);

  // IER/ISR: bits[1:0]
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_IER) |=> RVALID
                   && RDATA[1:0]==$past(int_ier) && RDATA[31:2]==30'h0);
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_ISR) |=> RVALID
                   && RDATA[1:0]==$past(int_isr) && RDATA[31:2]==30'h0);

  // A, B, ACCUM full data
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_A_DATA_0)     |=> RVALID && RDATA===$past(int_a));
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_B_DATA_0)     |=> RVALID && RDATA===$past(int_b));
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_ACCUM_DATA_0) |=> RVALID && RDATA===$past(int_accum));

  // ACCUM_CTRL: bit0=vld
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_ACCUM_CTRL) |=> RVALID
                   && RDATA[0]==$past(int_accum_ap_vld) && RDATA[31:1]==31'h0);

  // ACCUM_CLR: bit0
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_ACCUM_CLR_DATA_0) |=> RVALID
                   && RDATA[0]==$past(int_accum_clr[0]) && RDATA[31:1]==31'h0);

  // Unmapped read returns zero
  assert property (ACLK_EN && ar_hs && !(raddr inside {
                    ADDR_AP_CTRL,ADDR_GIE,ADDR_IER,ADDR_ISR,
                    ADDR_A_DATA_0,ADDR_B_DATA_0,
                    ADDR_ACCUM_DATA_0,ADDR_ACCUM_CTRL,
                    ADDR_ACCUM_CLR_DATA_0
                   }) |=> RVALID && (RDATA==32'h0));

  // ---------------- Register side-effects and semantics ----------------

  // ap_start: write-1 to start; ap_ready updates to auto_restart; write has priority
  assert property (ACLK_EN && w_hs && (waddr==ADDR_AP_CTRL) && WSTRB[0] && WDATA[0] |=> int_ap_start);
  assert property (ACLK_EN && ap_ready && !(w_hs && (waddr==ADDR_AP_CTRL) && WSTRB[0] && WDATA[0])
                   |=> int_ap_start == $past(int_auto_restart));

  // ap_done sticky and clear-on-read (unless set same cycle)
  assert property (ACLK_EN && ap_done |=> int_ap_done);
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_AP_CTRL) && !ap_done |=> !int_ap_done);

  // auto_restart and GIE/IER writes
  assert property (ACLK_EN && w_hs && (waddr==ADDR_AP_CTRL) && WSTRB[0]
                   |=> int_auto_restart == $past(WDATA[7]));
  assert property (ACLK_EN && w_hs && (waddr==ADDR_GIE) && WSTRB[0]
                   |=> int_gie == $past(WDATA[0]));
  assert property (ACLK_EN && w_hs && (waddr==ADDR_IER) && WSTRB[0]
                   |=> int_ier == $past(WDATA[1:0]));

  // ISR set by events (when enabled), XOR-toggled by write-1 (unless event same cycle)
  assert property (ACLK_EN && int_ier[0] && ap_done  |=> int_isr[0]);
  assert property (ACLK_EN && int_ier[1] && ap_ready |=> int_isr[1]);
  assert property (ACLK_EN && w_hs && (waddr==ADDR_ISR) && WSTRB[0]
                   && !(int_ier[0] && ap_done) && !(int_ier[1] && ap_ready)
                   |=> int_isr[1:0] == ($past(int_isr[1:0]) ^ $past(WDATA[1:0])));

  // Interrupt line equals GIE ANDed with any ISR
  assert property (interrupt == (int_gie & (|int_isr)));

  // A/B write with byte enables
  assert property (ACLK_EN && w_hs && (waddr==ADDR_A_DATA_0)
                   |=> int_a == (($past(WDATA) & $past(wmask)) | ($past(int_a) & ~$past(wmask))));
  assert property (ACLK_EN && w_hs && (waddr==ADDR_B_DATA_0)
                   |=> int_b == (($past(WDATA) & $past(wmask)) | ($past(int_b) & ~$past(wmask))));

  // ACCUM capture and valid flag sticky until read
  assert property (ACLK_EN && accum_ap_vld |=> (int_accum == $past(accum)) && int_accum_ap_vld);
  assert property (ACLK_EN && ar_hs && (raddr==ADDR_ACCUM_CTRL) && !accum_ap_vld |=> !int_accum_ap_vld);

  // ACCUM_CLR bit write behavior (only bit0 affected by WSTRB[0])
  assert property (ACLK_EN && w_hs && (waddr==ADDR_ACCUM_CLR_DATA_0)
                   |=> int_accum_clr[0] == ($past(WSTRB[0]) ? $past(WDATA[0]) : $past(int_accum_clr[0])));

  // ---------------- Basic reset postconditions ----------------
  assert property ($rose(ARESET) |-> !BVALID && !RVALID);

  // ---------------- Coverage ----------------
  // One complete write txn then response
  cover property (ACLK_EN && (wstate==WRIDLE) && AWVALID && AWREADY ##1
                  (wstate==WRDATA) && WVALID && WREADY ##1
                  (wstate==WRRESP) && BVALID && BREADY);

  // One complete read txn then response
  cover property (ACLK_EN && (rstate==RDIDLE) && ARVALID && ARREADY ##1
                  (rstate==RDDATA) && RVALID && RREADY);

  // Start pulse then ready with auto_restart=0 and =1
  cover property (ACLK_EN && w_hs && (waddr==ADDR_AP_CTRL) && WSTRB[0] && (WDATA[0]==1'b1) ##[1:$]
                  ap_ready && (int_auto_restart==1'b0));
  cover property (ACLK_EN && w_hs && (waddr==ADDR_AP_CTRL) && WSTRB[0] && (WDATA[7]==1'b1) ##1
                  w_hs && (waddr==ADDR_AP_CTRL) && WSTRB[0] && (WDATA[0]==1'b1) ##[1:$]
                  ap_ready && (int_auto_restart==1'b1));

  // ISR set by event, interrupt asserted, then cleared via write-1
  cover property (ACLK_EN && (int_ier[0]==1) ##1 ap_done ##1 int_isr[0] && interrupt ##1
                  w_hs && (waddr==ADDR_ISR) && WSTRB[0] && (WDATA[0]==1) ##1 !interrupt);

  // Read ACCUM_CTRL clears valid flag
  cover property (ACLK_EN && accum_ap_vld ##1 ar_hs && (raddr==ADDR_ACCUM_CTRL) ##1 !int_accum_ap_vld);

  // Partial byte write to A using WSTRB != 4'hF
  cover property (ACLK_EN && aw_hs && (AWADDR[ADDR_BITS-1:0]==ADDR_A_DATA_0) ##1
                  w_hs && (waddr==ADDR_A_DATA_0) && (WSTRB !== 4'hF));

endmodule