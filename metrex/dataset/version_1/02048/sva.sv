// SVA for DATA_PHYSICAL
// Bind into DUT; uses internal signals (STATE, NEXT_STATE, blocks, timeout_input)
module DATA_PHYSICAL_sva;
  default clocking cb @(posedge SD_CLK); endclocking
  default disable iff (!RESET_L);

  // Encoding checks
  a_onehot_state:     assert property ($onehot(STATE));
  a_onehot_nextstate: assert property ($onehot(NEXT_STATE));

  // Reset behavior
  a_sync_reset:       assert property (!RESET_L |=> STATE==RESET);
  a_reset_to_idle:    assert property (STATE==RESET |-> NEXT_STATE==IDLE);

  // IDLE branch
  a_idle_wr:          assert property (STATE==IDLE && strobe_IN_DATA_Phy && writeRead_DATA_Phy |-> NEXT_STATE==FIFO_READ);
  a_idle_rd:          assert property (STATE==IDLE && !(strobe_IN_DATA_Phy && writeRead_DATA_Phy) |-> NEXT_STATE==READ);
  a_idle_ready:       assert property (serial_Ready_Phy_DATA |-> STATE==IDLE);
  a_idle_timeoutclr:  assert property (STATE==IDLE |-> timeout_input==16'b0);

  // FIFO_READ
  a_fifo_read:        assert property (STATE==FIFO_READ |-> NEXT_STATE==LOAD_WRITE
                                       && writeFIFO_enable_Phy_FIFO
                                       && dataParallel_Phy_PS==dataFromFIFO_FIFO_Phy);

  // LOAD_WRITE
  a_load_write:       assert property (STATE==LOAD_WRITE |-> NEXT_STATE==SEND
                                       && enable_pts_Wrapper_Phy_PS
                                       && pad_enable_Phy_PAD
                                       && pad_state_Phy_PAD
                                       && !IO_enable_Phy_SD_CARD);

  // SEND
  a_send:             assert property (STATE==SEND |-> NEXT_STATE==WAIT_RESPONSE
                                       && IO_enable_Phy_SD_CARD);
  a_io_only_in_send:  assert property (IO_enable_Phy_SD_CARD |-> STATE==SEND);

  // WAIT_RESPONSE
  a_waitresp_ctrl:    assert property (STATE==WAIT_RESPONSE |-> enable_stp_Wrapper_Phy_SP && !enable_pts_Wrapper_Phy_PS && pad_state_Phy_PAD==0);
  a_waitresp_stay:    assert property (STATE==WAIT_RESPONSE && !reception_complete_SP_Phy |-> NEXT_STATE==WAIT_RESPONSE);
  a_waitresp_to_ack:  assert property (STATE==WAIT_RESPONSE && reception_complete_SP_Phy && (!multiple_DATA_Phy || (blocks==blocks_DATA_Phy)) |-> NEXT_STATE==WAIT_ACK);
  a_waitresp_more:    assert property (STATE==WAIT_RESPONSE && reception_complete_SP_Phy && ( multiple_DATA_Phy && !(blocks==blocks_DATA_Phy)) |-> NEXT_STATE==FIFO_READ);
  a_waitresp_to:      assert property (STATE==WAIT_RESPONSE && (timeout_input==timeout_Reg_DATA_Phy) |-> data_timeout_Phy_DATA);
  a_waitresp_not_to:  assert property (STATE==WAIT_RESPONSE && !(timeout_input==timeout_Reg_DATA_Phy) |-> !data_timeout_Phy_DATA);

  // READ
  a_read_ctrl:        assert property (STATE==READ |-> enable_stp_Wrapper_Phy_SP && pad_enable_Phy_PAD && pad_state_Phy_PAD==0);
  a_read_stay:        assert property (STATE==READ && !reception_complete_SP_Phy |-> NEXT_STATE==READ);
  a_read_to_fifo:     assert property (STATE==READ && reception_complete_SP_Phy |-> NEXT_STATE==READ_FIFO_WRITE);
  a_read_to:          assert property (STATE==READ && (timeout_input==timeout_Reg_DATA_Phy) |-> data_timeout_Phy_DATA);
  a_read_not_to:      assert property (STATE==READ && !(timeout_input==timeout_Reg_DATA_Phy) |-> !data_timeout_Phy_DATA);

  // READ_FIFO_WRITE
  a_rfw_sideeffects:  assert property (STATE==READ_FIFO_WRITE |-> readFIFO_enable_Phy_FIFO
                                       && dataReadToFIFO_Phy_FIFO==data_read_SP_Phy
                                       && !enable_stp_Wrapper_Phy_SP);
  a_rfw_to_ack:       assert property (STATE==READ_FIFO_WRITE && ((blocks==blocks_DATA_Phy) || !multiple_DATA_Phy) |-> NEXT_STATE==WAIT_ACK);
  a_rfw_more:         assert property (STATE==READ_FIFO_WRITE && (multiple_DATA_Phy && (blocks!=blocks_DATA_Phy)) |-> NEXT_STATE==READ_WRAPPER_RESET);

  // READ_WRAPPER_RESET
  a_rwr_to_read:      assert property (STATE==READ_WRAPPER_RESET |-> reset_Wrapper_Phy_PS && NEXT_STATE==READ);

  // WAIT_ACK
  a_waitack_done:     assert property (STATE==WAIT_ACK |-> complete_Phy_DATA);
  a_complete_only:    assert property (complete_Phy_DATA |-> STATE==WAIT_ACK);
  a_waitack_hold:     assert property (STATE==WAIT_ACK && !ack_IN_DATA_Phy |-> NEXT_STATE==WAIT_ACK);
  a_waitack_to_send:  assert property (STATE==WAIT_ACK &&  ack_IN_DATA_Phy |-> NEXT_STATE==SEND_ACK);

  // SEND_ACK
  a_sendack:          assert property (STATE==SEND_ACK |-> ack_OUT_Phy_DATA && NEXT_STATE==IDLE);
  a_ackout_only:      assert property (ack_OUT_Phy_DATA |-> STATE==SEND_ACK);

  // Internal counters/latches behavior
  a_to_stable_else:   assert property (!(STATE inside {IDLE,READ,WAIT_RESPONSE}) |-> $stable(timeout_input));
  a_blk_stable_else:  assert property (!(STATE inside {IDLE,READ,WAIT_RESPONSE}) |-> $stable(blocks));
  a_to_incr_hold:     assert property ((STATE inside {READ,WAIT_RESPONSE}) && NEXT_STATE==STATE |=> timeout_input==$past(timeout_input)+1);
  a_to_monotonic:     assert property ((STATE inside {READ,WAIT_RESPONSE}) |=> timeout_input >= $past(timeout_input));

  // No X after reset deassert
  a_no_x:             assert property (!$isunknown({serial_Ready_Phy_DATA, complete_Phy_DATA, ack_OUT_Phy_DATA, data_timeout_Phy_DATA,
                                                   reset_Wrapper_Phy_PS, enable_pts_Wrapper_Phy_PS, enable_stp_Wrapper_Phy_SP,
                                                   dataParallel_Phy_PS, pad_state_Phy_PAD, pad_enable_Phy_PAD,
                                                   writeFIFO_enable_Phy_FIFO, readFIFO_enable_Phy_FIFO,
                                                   dataReadToFIFO_Phy_FIFO, IO_enable_Phy_SD_CARD, STATE, NEXT_STATE}));

  // Coverage
  c_reset_to_idle:    cover property (STATE==RESET ##1 STATE==IDLE);

  // Write, single-block
  c_write_single:     cover property (STATE==IDLE && strobe_IN_DATA_Phy && writeRead_DATA_Phy
                                      ##1 STATE==FIFO_READ ##1 STATE==LOAD_WRITE ##1 STATE==SEND
                                      ##1 STATE==WAIT_RESPONSE ##[1:5] reception_complete_SP_Phy
                                      ##1 STATE==WAIT_ACK ##1 ack_IN_DATA_Phy ##1 STATE==SEND_ACK ##1 STATE==IDLE);

  // Write, multi-block loop
  c_write_multi:      cover property (STATE==WAIT_RESPONSE && reception_complete_SP_Phy && multiple_DATA_Phy && (blocks!=blocks_DATA_Phy)
                                      ##1 STATE==FIFO_READ);

  // Read, single-block
  c_read_single:      cover property (STATE==IDLE && !(strobe_IN_DATA_Phy && writeRead_DATA_Phy)
                                      ##1 STATE==READ ##[1:5] reception_complete_SP_Phy
                                      ##1 STATE==READ_FIFO_WRITE ##1 STATE==WAIT_ACK ##1 ack_IN_DATA_Phy ##1 STATE==SEND_ACK);

  // Timeout event in READ/WAIT_RESPONSE
  c_timeout:          cover property ((STATE inside {READ,WAIT_RESPONSE}) ##[1:$] (timeout_input==timeout_Reg_DATA_Phy) and data_timeout_Phy_DATA);
endmodule

bind DATA_PHYSICAL DATA_PHYSICAL_sva u_DATA_PHYSICAL_sva();