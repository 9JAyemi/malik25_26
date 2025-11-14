// SVA for pcieCore_gtp_pipe_rate
// Bind into DUT scope to access internals
module pcieCore_gtp_pipe_rate_sva;

  // Param snapshot for path selection
  localparam bit SIM = (PCIE_SIM_SPEEDUP == "TRUE");

  default clocking cb @(posedge RATE_CLK); endclocking
  default disable iff (!RATE_RST_N);

  // No X on key signals post-reset
  a_no_x_outs:  assert property (!$isunknown({RATE_PCLK_SEL, RATE_DRP_START, RATE_DRP_X16, RATE_RATE_OUT, RATE_TXSYNC_START, RATE_DONE, RATE_IDLE, RATE_FSM})));
  a_no_x_state: assert property (!$isunknown({fsm, pclk_sel, rate_out, txdata_wait_cnt})));

  // FSM validity
  a_fsm_valid: assert property (fsm inside {
    FSM_IDLE, FSM_TXDATA_WAIT, FSM_PCLK_SEL, FSM_DRP_X16_START, FSM_DRP_X16_DONE,
    FSM_RATE_SEL, FSM_RXPMARESETDONE, FSM_DRP_X20_START, FSM_DRP_X20_DONE,
    FSM_RATE_DONE, FSM_TXSYNC_START, FSM_TXSYNC_DONE, FSM_DONE
  });

  // Output encodings/mirroring
  a_rate_fsm_match:     assert property ({1'b0,fsm} == RATE_FSM);
  a_idle_o:             assert property (RATE_IDLE == (fsm == FSM_IDLE));
  a_done_o:             assert property (RATE_DONE == (fsm == FSM_DONE));
  a_txsync_start_o:     assert property (RATE_TXSYNC_START == (fsm == FSM_TXSYNC_START));
  a_drp_start_o:        assert property (RATE_DRP_START == ((fsm == FSM_DRP_X16_START) || (fsm == FSM_DRP_X20_START)));
  a_drp_x16_o:          assert property (RATE_DRP_X16   == ((fsm == FSM_DRP_X16_START) || (fsm == FSM_DRP_X16_DONE)));
  a_pclk_sel_o:         assert property (RATE_PCLK_SEL  == pclk_sel);
  a_rate_out_o:         assert property (RATE_RATE_OUT  == rate_out);
  a_rateout_range:      assert property (RATE_RATE_OUT inside {[0:1]});

  // 2-flop synchronizers
  a_sync_rate:    assert property ($past(RATE_RST_N) |-> (rate_in_reg1        == $past(RATE_RATE_IN)));
  a_sync_rate2:   assert property ($past(RATE_RST_N) |-> (rate_in_reg2        == $past(rate_in_reg1)));
  a_sync_drp:     assert property ($past(RATE_RST_N) |-> (drp_done_reg1       == $past(RATE_DRP_DONE)       && drp_done_reg2       == $past(drp_done_reg1)));
  a_sync_rxpma:   assert property ($past(RATE_RST_N) |-> (rxpmaresetdone_reg1 == $past(RATE_RXPMARESETDONE) && rxpmaresetdone_reg2 == $past(rxpmaresetdone_reg1)));
  a_sync_txrate:  assert property ($past(RATE_RST_N) |-> (txratedone_reg1     == $past(RATE_TXRATEDONE)     && txratedone_reg2     == $past(txratedone_reg1)));
  a_sync_rxrate:  assert property ($past(RATE_RST_N) |-> (rxratedone_reg1     == $past(RATE_RXRATEDONE)     && rxratedone_reg2     == $past(rxratedone_reg1)));
  a_sync_phy:     assert property ($past(RATE_RST_N) |-> (phystatus_reg1      == $past(RATE_PHYSTATUS)      && phystatus_reg2      == $past(phystatus_reg1)));
  a_sync_txsync:  assert property ($past(RATE_RST_N) |-> (txsync_done_reg1    == $past(RATE_TXSYNC_DONE)    && txsync_done_reg2    == $past(txsync_done_reg1)));

  // txdata_wait_cnt behavior
  a_cnt_inc: assert property (fsm == FSM_TXDATA_WAIT && txdata_wait_cnt < TXDATA_WAIT_MAX |=> txdata_wait_cnt == $past(txdata_wait_cnt)+1);
  a_cnt_sat: assert property (fsm == FSM_TXDATA_WAIT && txdata_wait_cnt == TXDATA_WAIT_MAX |=> txdata_wait_cnt == TXDATA_WAIT_MAX);
  a_cnt_clr: assert property (fsm != FSM_TXDATA_WAIT |=> txdata_wait_cnt == 0);

  // pclk_sel / rate_out update and stability
  a_pclk_update: assert property (fsm == FSM_PCLK_SEL |=> pclk_sel == (rate_in_reg2 == 2'd1));
  a_pclk_stable: assert property (fsm != FSM_PCLK_SEL |=> pclk_sel == $past(pclk_sel));
  a_rate_update: assert property (fsm == FSM_RATE_SEL |=> rate_out == rate);
  a_rate_stable: assert property (fsm != FSM_RATE_SEL |=> rate_out == $past(rate_out));

  // ratedone/flags gating and causality
  function automatic bit in_latch_states;
    return (fsm == FSM_RATE_DONE) || (fsm == FSM_RXPMARESETDONE) || (fsm == FSM_DRP_X20_START) || (fsm == FSM_DRP_X20_DONE);
  endfunction
  a_flags_zero_outside:    assert property (!in_latch_states() |=> (!txratedone && !rxratedone && !phystatus && !ratedone));
  a_rise_txratedone_src:   assert property ($rose(txratedone) |-> txratedone_reg2);
  a_rise_rxratedone_src:   assert property ($rose(rxratedone) |-> rxratedone_reg2);
  a_rise_phystatus_src:    assert property ($rose(phystatus)  |-> phystatus_reg2);
  a_ratedone_implies_all:  assert property (ratedone |-> (txratedone && rxratedone && phystatus));
  a_rise_ratedone_src:     assert property ($rose(ratedone) |-> (txratedone && rxratedone && phystatus));

  // Next-state transition checks
  a_idle_stay:      assert property (fsm == FSM_IDLE && (rate_in_reg2 == rate_in_reg1) |=> fsm == FSM_IDLE);
  a_idle_to_wait:   assert property (fsm == FSM_IDLE && (rate_in_reg2 != rate_in_reg1) |=> fsm == FSM_TXDATA_WAIT);

  a_wait_stay:      assert property (fsm == FSM_TXDATA_WAIT && txdata_wait_cnt < TXDATA_WAIT_MAX |=> fsm == FSM_TXDATA_WAIT);
  a_wait_to_pclk:   assert property (fsm == FSM_TXDATA_WAIT && txdata_wait_cnt == TXDATA_WAIT_MAX |=> fsm == FSM_PCLK_SEL);

  generate
    if (SIM) begin
      a_pclk_to_rate_sel:        assert property (fsm == FSM_PCLK_SEL |=> fsm == FSM_RATE_SEL);
      a_rate_sel_to_rate_done:   assert property (fsm == FSM_RATE_SEL |=> fsm == FSM_RATE_DONE);
    end else begin
      a_pclk_to_drp16:           assert property (fsm == FSM_PCLK_SEL |=> fsm == FSM_DRP_X16_START);
      a_drp16_start_to_done:     assert property (fsm == FSM_DRP_X16_START && !drp_done_reg2 |=> fsm == FSM_DRP_X16_DONE);
      a_drp16_start_stay:        assert property (fsm == FSM_DRP_X16_START &&  drp_done_reg2 |=> fsm == FSM_DRP_X16_START);
      a_drp16_done_to_rate_sel:  assert property (fsm == FSM_DRP_X16_DONE  &&  drp_done_reg2 |=> fsm == FSM_RATE_SEL);
      a_drp16_done_stay:         assert property (fsm == FSM_DRP_X16_DONE  && !drp_done_reg2 |=> fsm == FSM_DRP_X16_DONE);
      a_rate_sel_to_rxpma:       assert property (fsm == FSM_RATE_SEL |=> fsm == FSM_RXPMARESETDONE);
      a_rxpma_to_drp20:          assert property (fsm == FSM_RXPMARESETDONE && !rxpmaresetdone_reg2 |=> fsm == FSM_DRP_X20_START);
      a_rxpma_stay:              assert property (fsm == FSM_RXPMARESETDONE &&  rxpmaresetdone_reg2 |=> fsm == FSM_RXPMARESETDONE);
      a_drp20_start_to_done:     assert property (fsm == FSM_DRP_X20_START && !drp_done_reg2 |=> fsm == FSM_DRP_X20_DONE);
      a_drp20_start_stay:        assert property (fsm == FSM_DRP_X20_START &&  drp_done_reg2 |=> fsm == FSM_DRP_X20_START);
      a_drp20_done_to_rate_done: assert property (fsm == FSM_DRP_X20_DONE  &&  drp_done_reg2 |=> fsm == FSM_RATE_DONE);
      a_drp20_done_stay:         assert property (fsm == FSM_DRP_X20_DONE  && !drp_done_reg2 |=> fsm == FSM_DRP_X20_DONE);
    end
  endgenerate

  a_rate_done_stay:        assert property (fsm == FSM_RATE_DONE && !ratedone |=> fsm == FSM_RATE_DONE);
  a_rate_done_to_txsync:   assert property (fsm == FSM_RATE_DONE &&  ratedone |=> fsm == FSM_TXSYNC_START);

  a_txsync_start_to_done:  assert property (fsm == FSM_TXSYNC_START && !txsync_done_reg2 |=> fsm == FSM_TXSYNC_DONE);
  a_txsync_start_stay:     assert property (fsm == FSM_TXSYNC_START &&  txsync_done_reg2 |=> fsm == FSM_TXSYNC_START);

  a_txsync_done_to_done:   assert property (fsm == FSM_TXSYNC_DONE &&  txsync_done_reg2 |=> fsm == FSM_DONE);
  a_txsync_done_stay:      assert property (fsm == FSM_TXSYNC_DONE && !txsync_done_reg2 |=> fsm == FSM_TXSYNC_DONE);

  a_done_to_idle:          assert property (fsm == FSM_DONE |=> fsm == FSM_IDLE);

  // Coverage
  c_rate0: cover property (fsm == FSM_RATE_SEL ##1 rate_out == 3'd0);
  c_rate1: cover property (fsm == FSM_RATE_SEL ##1 rate_out == 3'd1);

  generate
    if (SIM) begin
      c_full_flow_sim: cover property (
        (fsm == FSM_IDLE && rate_in_reg2 != rate_in_reg1)
        ##1 (fsm == FSM_TXDATA_WAIT)
        ##[1:TXDATA_WAIT_MAX+2] (fsm == FSM_PCLK_SEL)
        ##1 (fsm == FSM_RATE_SEL)
        ##1 (fsm == FSM_RATE_DONE)
        ##[1:$] (fsm == FSM_TXSYNC_START)
        ##[1:$] (fsm == FSM_TXSYNC_DONE)
        ##1 (fsm == FSM_DONE)
        ##1 (fsm == FSM_IDLE)
      );
    end else begin
      c_full_flow: cover property (
        (fsm == FSM_IDLE && rate_in_reg2 != rate_in_reg1)
        ##1 (fsm == FSM_TXDATA_WAIT)
        ##[1:TXDATA_WAIT_MAX+2] (fsm == FSM_PCLK_SEL)
        ##1 (fsm == FSM_DRP_X16_START)
        ##[1:$] (fsm == FSM_DRP_X16_DONE)
        ##1 (fsm == FSM_RATE_SEL)
        ##1 (fsm == FSM_RXPMARESETDONE)
        ##[1:$] (fsm == FSM_DRP_X20_START)
        ##[1:$] (fsm == FSM_DRP_X20_DONE)
        ##1 (fsm == FSM_RATE_DONE)
        ##[1:$] (fsm == FSM_TXSYNC_START)
        ##[1:$] (fsm == FSM_TXSYNC_DONE)
        ##1 (fsm == FSM_DONE)
        ##1 (fsm == FSM_IDLE)
      );
    end
  endgenerate

endmodule

bind pcieCore_gtp_pipe_rate pcieCore_gtp_pipe_rate_sva;