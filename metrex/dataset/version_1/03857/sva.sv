// SVA checker for aq_axi_memcpy32_ctl
// Bind this checker to the DUT: bind aq_axi_memcpy32_ctl aq_axi_memcpy32_ctl_sva chk(.dut());

module aq_axi_memcpy32_ctl_sva (aq_axi_memcpy32_ctl dut);

  // Mirror state encodings to avoid hierarchical param dependency
  localparam int S_IDLE       = 0;
  localparam int S_READ_PRE   = 1;
  localparam int S_READ       = 2;
  localparam int S_READ_WAIT  = 3;
  localparam int S_WRITE_PRE  = 4;
  localparam int S_WRITE      = 5;
  localparam int S_WRITE_WAIT = 6;

  default clocking cb @(posedge dut.CLK); endclocking
  default disable iff (!dut.RST_N)

  // Basic sanity
  assert property (dut.state inside {[S_IDLE:S_WRITE_WAIT]});
  assert property (!$isunknown({dut.state, dut.WR_START, dut.RD_START, dut.CMD_READY, dut.CMD_DONE, dut.FIFO_RST,
                                dut.WR_ADRS, dut.WR_COUNT, dut.RD_ADRS, dut.RD_COUNT}));

  // Reset behavior (while in reset)
  assert property (!dut.RST_N |-> dut.state == S_IDLE
                                  && dut.reg_wr_adrs == 32'd0 && dut.reg_rd_adrs == 32'd0
                                  && dut.reg_wr_count == 32'd0 && dut.reg_rd_count == 32'd0);

  // Output/state mapping
  assert property (dut.RD_START == (dut.state == S_READ));
  assert property (dut.WR_START == (dut.state == S_WRITE));
  assert property (dut.CMD_READY == (dut.state == S_IDLE));
  assert property (dut.CMD_DONE  == (dut.state == S_IDLE));
  assert property (dut.FIFO_RST  == (dut.state == S_IDLE));

  // No overlap of start pulses; one-cycle pulses
  assert property (!(dut.RD_START && dut.WR_START));
  assert property (dut.RD_START |=> !dut.RD_START);
  assert property (dut.WR_START |=> !dut.WR_START);

  // Data path outputs reflect latched regs
  assert property ({dut.WR_ADRS, dut.WR_COUNT, dut.RD_ADRS, dut.RD_COUNT} ==
                   {dut.reg_wr_adrs, dut.reg_wr_count, dut.reg_rd_adrs, dut.reg_rd_count});

  // Register load on CMD_REQ in IDLE, and stability while busy
  assert property (dut.state == S_IDLE && dut.CMD_REQ |=> dut.state == S_READ_PRE
                   && dut.reg_wr_adrs  == $past(dut.CMD_DST)
                   && dut.reg_wr_count == $past(dut.CMD_LEN)
                   && dut.reg_rd_adrs  == $past(dut.CMD_SRC)
                   && dut.reg_rd_count == $past(dut.CMD_LEN));
  assert property (dut.state == S_IDLE && !dut.CMD_REQ |=> dut.state == S_IDLE
                   && $stable({dut.reg_wr_adrs, dut.reg_wr_count, dut.reg_rd_adrs, dut.reg_rd_count}));
  assert property (dut.state != S_IDLE |-> $stable({dut.reg_wr_adrs, dut.reg_wr_count, dut.reg_rd_adrs, dut.reg_rd_count}));

  // FSM transition legality
  assert property (dut.state == S_IDLE       &&  dut.CMD_REQ  |=> dut.state == S_READ_PRE);
  assert property (dut.state == S_IDLE       && !dut.CMD_REQ  |=> dut.state == S_IDLE);

  assert property (dut.state == S_READ_PRE   &&  dut.WR_READY |=> dut.state == S_READ);
  assert property (dut.state == S_READ_PRE   && !dut.WR_READY |=> dut.state == S_READ_PRE);

  assert property (dut.state == S_READ                        |=> dut.state == S_READ_WAIT);

  assert property (dut.state == S_READ_WAIT &&  dut.WR_READY |=> dut.state == S_WRITE_PRE);
  assert property (dut.state == S_READ_WAIT && !dut.WR_READY |=> dut.state == S_READ_WAIT);

  assert property (dut.state == S_WRITE_PRE  &&  dut.RD_READY |=> dut.state == S_WRITE);
  assert property (dut.state == S_WRITE_PRE  && !dut.RD_READY |=> dut.state == S_WRITE_PRE);

  assert property (dut.state == S_WRITE                       |=> dut.state == S_WRITE_WAIT);

  assert property (dut.state == S_WRITE_WAIT &&  dut.RD_READY |=> dut.state == S_IDLE);
  assert property (dut.state == S_WRITE_WAIT && !dut.RD_READY |=> dut.state == S_WRITE_WAIT);

  // Coverage: full transaction (allows stalls in *_PRE/WAIT)
  sequence s_txn;
    dut.state == S_IDLE && dut.CMD_REQ ##1
    (dut.state == S_READ_PRE)[*1:$] ##1
    dut.state == S_READ ##1
    (dut.state == S_READ_WAIT)[*1:$] ##1
    (dut.state == S_WRITE_PRE)[*1:$] ##1
    dut.state == S_WRITE ##1
    (dut.state == S_WRITE_WAIT)[*1:$] ##1
    dut.state == S_IDLE;
  endsequence
  cover property (s_txn);
  cover property (dut.RD_START ##[1:$] dut.WR_START);      // both start pulses seen
  cover property (dut.state == S_IDLE && dut.CMD_REQ && dut.CMD_LEN == 32'd0); // zero-length cmd
  cover property (s_txn ##1 (dut.CMD_REQ && dut.state == S_IDLE));             // back-to-back cmds

endmodule