// SVA for speed_neg_control
// Bind module
module speed_neg_control_sva_bind (speed_neg_control dut);
  localparam [4:0]
    IDLE            = dut.IDLE,
    READ_GEN2       = dut.READ_GEN2,
    WRITE_GEN2      = dut.WRITE_GEN2,
    COMPLETE_GEN2   = dut.COMPLETE_GEN2,
    PAUSE1_GEN2     = dut.PAUSE1_GEN2,
    READ1_GEN2      = dut.READ1_GEN2,
    WRITE1_GEN2     = dut.WRITE1_GEN2,
    COMPLETE1_GEN2  = dut.COMPLETE1_GEN2,
    RESET_          = dut.RESET,
    WAIT_GEN2       = dut.WAIT_GEN2,
    READ_GEN1       = dut.READ_GEN1,
    WRITE_GEN1      = dut.WRITE_GEN1,
    COMPLETE_GEN1   = dut.COMPLETE_GEN1,
    PAUSE_GEN1      = dut.PAUSE_GEN1,
    READ1_GEN1      = dut.READ1_GEN1,
    WRITE1_GEN1     = dut.WRITE1_GEN1,
    COMPLETE1_GEN1  = dut.COMPLETE1_GEN1,
    RESET_GEN1      = dut.RESET_GEN1,
    WAIT_GEN1       = dut.WAIT_GEN1,
    LINKUP          = dut.LINKUP;

  wire        clk   = dut.clk;
  wire        rst   = dut.reset;
  wire [4:0]  st    = dut.state_out;

  // Reset initialization
  ap_reset_init: assert property (@(posedge clk)
    rst |-> st==IDLE && dut.daddr==7'h00 && dut.di==16'h0000 && dut.den==1'b0 &&
           dut.dwe==1'b0 && dut.gen_value==1'b1 && dut.mgt_reset==1'b0);

  // Legal next-state transitions
  ap_tr_idle:          assert property (@(posedge clk) disable iff (rst) st==IDLE         |=> st inside {IDLE, READ_GEN2});
  ap_tr_read_g2:       assert property (@(posedge clk) disable iff (rst) st==READ_GEN2    |=> st inside {READ_GEN2, WRITE_GEN2});
  ap_tr_write_g2:      assert property (@(posedge clk) disable iff (rst) st==WRITE_GEN2   |=> st==COMPLETE_GEN2);
  ap_tr_cmpl_g2:       assert property (@(posedge clk) disable iff (rst) st==COMPLETE_GEN2|=> st inside {COMPLETE_GEN2, PAUSE1_GEN2});
  ap_tr_pause1_g2:     assert property (@(posedge clk) disable iff (rst) st==PAUSE1_GEN2  |=> st inside {PAUSE1_GEN2, READ1_GEN2});
  ap_tr_read1_g2:      assert property (@(posedge clk) disable iff (rst) st==READ1_GEN2   |=> st inside {READ1_GEN2, WRITE1_GEN2});
  ap_tr_write1_g2:     assert property (@(posedge clk) disable iff (rst) st==WRITE1_GEN2  |=> st==COMPLETE1_GEN2);
  ap_tr_cmpl1_g2:      assert property (@(posedge clk) disable iff (rst) st==COMPLETE1_GEN2|=> st inside {COMPLETE1_GEN2, RESET_});
  ap_tr_reset_g2:      assert property (@(posedge clk) disable iff (rst) st==RESET_       |=> st inside {RESET_, WAIT_GEN2});
  ap_tr_wait_g2:       assert property (@(posedge clk) disable iff (rst) st==WAIT_GEN2    |=> st inside {WAIT_GEN2, LINKUP, READ_GEN1});
  ap_tr_read_g1:       assert property (@(posedge clk) disable iff (rst) st==READ_GEN1    |=> st inside {READ_GEN1, WRITE_GEN1});
  ap_tr_write_g1:      assert property (@(posedge clk) disable iff (rst) st==WRITE_GEN1   |=> st==COMPLETE_GEN1);
  ap_tr_cmpl_g1:       assert property (@(posedge clk) disable iff (rst) st==COMPLETE_GEN1|=> st inside {COMPLETE_GEN1, PAUSE_GEN1});
  ap_tr_pause_g1:      assert property (@(posedge clk) disable iff (rst) st==PAUSE_GEN1   |=> st inside {PAUSE_GEN1, READ1_GEN1});
  ap_tr_read1_g1:      assert property (@(posedge clk) disable iff (rst) st==READ1_GEN1   |=> st inside {READ1_GEN1, WRITE1_GEN1});
  ap_tr_write1_g1:     assert property (@(posedge clk) disable iff (rst) st==WRITE1_GEN1  |=> st==COMPLETE1_GEN1);
  ap_tr_cmpl1_g1:      assert property (@(posedge clk) disable iff (rst) st==COMPLETE1_GEN1|=> st inside {COMPLETE1_GEN1, RESET_GEN1});
  ap_tr_reset_g1:      assert property (@(posedge clk) disable iff (rst) st==RESET_GEN1   |=> st inside {RESET_GEN1, WAIT_GEN1});
  ap_tr_wait_g1:       assert property (@(posedge clk) disable iff (rst) st==WAIT_GEN1    |=> st inside {WAIT_GEN1, LINKUP, READ_GEN2});
  ap_tr_linkup:        assert property (@(posedge clk) disable iff (rst) st==LINKUP       |=> st inside {LINKUP, READ_GEN2});

  // Entry-side effects into READ states
  ap_enter_read_g2:    assert property (@(posedge clk) disable iff (rst) st==READ_GEN2  |-> dut.den && dut.daddr==7'h46);
  ap_enter_read1_g2:   assert property (@(posedge clk) disable iff (rst) st==READ1_GEN2 |-> dut.den && dut.daddr==7'h45);
  ap_enter_read_g1:    assert property (@(posedge clk) disable iff (rst) st==READ_GEN1  |-> dut.den && dut.daddr==7'h46 && dut.gen_value==1'b0);
  ap_enter_read1_g1:   assert property (@(posedge clk) disable iff (rst) st==READ1_GEN1 |-> dut.den && dut.daddr==7'h45);

  // IDLE lock kick-off to GEN2
  ap_idle_lock:        assert property (@(posedge clk) disable iff (rst)
                              st==IDLE && dut.gtp_lock |=> st==READ_GEN2 && dut.den && dut.daddr==7'h46 && dut.gen_value==1'b1);
  ap_idle_no_lock:     assert property (@(posedge clk) disable iff (rst)
                              st==IDLE && !dut.gtp_lock |=> st==IDLE);

  // DRP READ handshake behavior
  ap_read_g2_hold:     assert property (@(posedge clk) disable iff (rst)
                              st==READ_GEN2 && !dut.drdy |=> st==READ_GEN2 && dut.den);
  ap_read_g2_advance:  assert property (@(posedge clk) disable iff (rst)
                              st==READ_GEN2 && dut.drdy  |=> st==WRITE_GEN2 && dut.den==1'b0);
  ap_read1_g2_hold:    assert property (@(posedge clk) disable iff (rst)
                              st==READ1_GEN2 && !dut.drdy |=> st==READ1_GEN2 && dut.den);
  ap_read1_g2_advance: assert property (@(posedge clk) disable iff (rst)
                              st==READ1_GEN2 && dut.drdy  |=> st==WRITE1_GEN2 && dut.den==1'b0);
  ap_read_g1_hold:     assert property (@(posedge clk) disable iff (rst)
                              st==READ_GEN1 && !dut.drdy |=> st==READ_GEN1 && dut.den);
  ap_read_g1_advance:  assert property (@(posedge clk) disable iff (rst)
                              st==READ_GEN1 && dut.drdy  |=> st==WRITE_GEN1 && dut.den==1'b0);
  ap_read1_g1_hold:    assert property (@(posedge clk) disable iff (rst)
                              st==READ1_GEN1 && !dut.drdy |=> st==READ1_GEN1 && dut.den);
  ap_read1_g1_advance: assert property (@(posedge clk) disable iff (rst)
                              st==READ1_GEN1 && dut.drdy  |=> st==WRITE1_GEN1 && dut.den==1'b0);

  // DRP WRITE cycle checks (den/dwe and bit forcing)
  ap_write_g2:         assert property (@(posedge clk) disable iff (rst)
                              st==WRITE_GEN2  |=> st==COMPLETE_GEN2  && dut.den && dut.dwe && dut.di[2]==1'b0);
  ap_write1_g2:        assert property (@(posedge clk) disable iff (rst)
                              st==WRITE1_GEN2 |=> st==COMPLETE1_GEN2 && dut.den && dut.dwe && dut.di[15]==1'b0);
  ap_write_g1:         assert property (@(posedge clk) disable iff (rst)
                              st==WRITE_GEN1  |=> st==COMPLETE_GEN1  && dut.den && dut.dwe && dut.di[2]==1'b1);
  ap_write1_g1:        assert property (@(posedge clk) disable iff (rst)
                              st==WRITE1_GEN1 |=> st==COMPLETE1_GEN1 && dut.den && dut.dwe && dut.di[15]==1'b1);

  // COMPLETE states hold den/dwe until drdy, then drop both
  ap_cmpl_g2_hold:     assert property (@(posedge clk) disable iff (rst)
                              st==COMPLETE_GEN2  && !dut.drdy |=> st==COMPLETE_GEN2  && dut.den && dut.dwe);
  ap_cmpl_g2_done:     assert property (@(posedge clk) disable iff (rst)
                              st==COMPLETE_GEN2  &&  dut.drdy |=> st==PAUSE1_GEN2    && !dut.den && !dut.dwe);
  ap_cmpl1_g2_hold:    assert property (@(posedge clk) disable iff (rst)
                              st==COMPLETE1_GEN2 && !dut.drdy |=> st==COMPLETE1_GEN2 && dut.den && dut.dwe);
  ap_cmpl1_g2_done:    assert property (@(posedge clk) disable iff (rst)
                              st==COMPLETE1_GEN2 &&  dut.drdy |=> st==RESET_         && !dut.den && !dut.dwe);
  ap_cmpl_g1_hold:     assert property (@(posedge clk) disable iff (rst)
                              st==COMPLETE_GEN1  && !dut.drdy |=> st==COMPLETE_GEN1  && dut.den && dut.dwe);
  ap_cmpl_g1_done:     assert property (@(posedge clk) disable iff (rst)
                              st==COMPLETE_GEN1  &&  dut.drdy |=> st==PAUSE_GEN1     && !dut.den && !dut.dwe);
  ap_cmpl1_g1_hold:    assert property (@(posedge clk) disable iff (rst)
                              st==COMPLETE1_GEN1 && !dut.drdy |=> st==COMPLETE1_GEN1 && dut.den && dut.dwe);
  ap_cmpl1_g1_done:    assert property (@(posedge clk) disable iff (rst)
                              st==COMPLETE1_GEN1 &&  dut.drdy |=> st==RESET_GEN1     && !dut.den && !dut.dwe);

  // WAIT transitions set up next read access
  ap_wait_g2_to_g1:    assert property (@(posedge clk) disable iff (rst)
                              $past(st)==WAIT_GEN2 && st==READ_GEN1 |-> $past(dut.gtp_lock) && dut.den && dut.daddr==7'h46 && dut.gen_value==1'b0);
  ap_wait_g1_to_g2:    assert property (@(posedge clk) disable iff (rst)
                              $past(st)==WAIT_GEN1 && st==READ_GEN2 |-> $past(dut.gtp_lock) && dut.den && dut.daddr==7'h46);

  // LINKUP hold and drop behavior
  ap_linkup_hold:      assert property (@(posedge clk) disable iff (rst)
                              st==LINKUP && dut.linkup |=> st==LINKUP);
  ap_linkup_drop_to_rd:assert property (@(posedge clk) disable iff (rst)
                              $past(st)==LINKUP && !dut.linkup && st==READ_GEN2 |-> dut.den && dut.daddr==7'h46);

  // mgt_reset only asserted in RESET states and deasserted on exit
  ap_mgtreset_scope:   assert property (@(posedge clk) disable iff (rst)
                              dut.mgt_reset |-> st inside {RESET_, RESET_GEN1});
  ap_reset_exit_g2:    assert property (@(posedge clk) disable iff (rst)
                              $past(st)==RESET_ && st==WAIT_GEN2 |-> $past(dut.mgt_reset)==1'b1 && dut.mgt_reset==1'b0);
  ap_reset_exit_g1:    assert property (@(posedge clk) disable iff (rst)
                              $past(st)==RESET_GEN1 && st==WAIT_GEN1 |-> $past(dut.mgt_reset)==1'b1 && dut.mgt_reset==1'b0);

  // dwe only during write/complete phases
  ap_dwe_gating:       assert property (@(posedge clk) disable iff (rst)
                              dut.dwe |-> st inside {WRITE_GEN2, COMPLETE_GEN2, WRITE1_GEN2, COMPLETE1_GEN2,
                                                     WRITE_GEN1, COMPLETE_GEN1, WRITE1_GEN1, COMPLETE1_GEN1});

  // Coverage: reach all states
  genvar i;
  // Explicit covers per state
  cover_idle:         cover property (@(posedge clk) st==IDLE);
  cover_read_g2:      cover property (@(posedge clk) st==READ_GEN2);
  cover_write_g2:     cover property (@(posedge clk) st==WRITE_GEN2);
  cover_cmpl_g2:      cover property (@(posedge clk) st==COMPLETE_GEN2);
  cover_pause1_g2:    cover property (@(posedge clk) st==PAUSE1_GEN2);
  cover_read1_g2:     cover property (@(posedge clk) st==READ1_GEN2);
  cover_write1_g2:    cover property (@(posedge clk) st==WRITE1_GEN2);
  cover_cmpl1_g2:     cover property (@(posedge clk) st==COMPLETE1_GEN2);
  cover_reset_g2:     cover property (@(posedge clk) st==RESET_);
  cover_wait_g2:      cover property (@(posedge clk) st==WAIT_GEN2);
  cover_read_g1:      cover property (@(posedge clk) st==READ_GEN1);
  cover_write_g1:     cover property (@(posedge clk) st==WRITE_GEN1);
  cover_cmpl_g1:      cover property (@(posedge clk) st==COMPLETE_GEN1);
  cover_pause_g1:     cover property (@(posedge clk) st==PAUSE_GEN1);
  cover_read1_g1:     cover property (@(posedge clk) st==READ1_GEN1);
  cover_write1_g1:    cover property (@(posedge clk) st==WRITE1_GEN1);
  cover_cmpl1_g1:     cover property (@(posedge clk) st==COMPLETE1_GEN1);
  cover_reset_g1:     cover property (@(posedge clk) st==RESET_GEN1);
  cover_wait_g1:      cover property (@(posedge clk) st==WAIT_GEN1);
  cover_linkup:       cover property (@(posedge clk) st==LINKUP);

  // Coverage: complete GEN2 reconfig sequence
  cover_gen2_path: cover property (@(posedge clk) disable iff (rst)
    st==READ_GEN2 ##1 st==WRITE_GEN2 ##[1:$] st==COMPLETE_GEN2 ##[1:$]
    st==PAUSE1_GEN2 ##[1:$] st==READ1_GEN2 ##1 st==WRITE1_GEN2 ##[1:$]
    st==COMPLETE1_GEN2 ##[1:$] st==RESET_ ##[1:$] st==WAIT_GEN2);

  // Coverage: complete GEN1 reconfig sequence
  cover_gen1_path: cover property (@(posedge clk) disable iff (rst)
    st==READ_GEN1 ##1 st==WRITE_GEN1 ##[1:$] st==COMPLETE_GEN1 ##[1:$]
    st==PAUSE_GEN1 ##[1:$] st==READ1_GEN1 ##1 st==WRITE1_GEN1 ##[1:$]
    st==COMPLETE1_GEN1 ##[1:$] st==RESET_GEN1 ##[1:$] st==WAIT_GEN1);

  // Coverage: speed toggle GEN2 -> GEN1 -> GEN2
  cover_speed_toggle: cover property (@(posedge clk) disable iff (rst)
    st==READ_GEN2 && dut.gen_value==1'b1 ##[1:$]
    st==READ_GEN1 && dut.gen_value==1'b0 ##[1:$]
    st==READ_GEN2);

endmodule

// Bind into DUT
bind speed_neg_control speed_neg_control_sva_bind sva_inst(.dut());