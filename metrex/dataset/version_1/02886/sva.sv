// SVA for data_transfer
// Bind into the DUT: bind data_transfer data_transfer_sva sva_inst();

module data_transfer_sva();
  // Clocking and reset control
  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RESET_L);

  // Reset defaults (override disable iff for this check)
  ap_reset_defaults: assert property (disable iff (1'b0)
    (!RESET_L |-> (timeout_counter==16'd0 &&
                   block_count==4'd0 &&
                   timeout_enable==1'b0 &&
                   multiple_data==1'b0 &&
                   write_read==1'b0 &&
                   ack_OUT_DATA_Phy==1'b0 &&
                   blocks_DATA_Phy==4'd0 &&
                   idle_out_DATA_Phy==1'b1 &&
                   strobe_OUT_DATA_Phy==1'b0 &&
                   transfer_complete_DATA_DMA==1'b0 &&
                   writeReadPhysical_DATA_Phy==1'b0 &&
                   multiple_DATA_Phy==1'b0 &&
                   complete_Phy_DATA==1'b0 &&
                   timeout_Phy_DATA==1'b0)));

  // Simple invariants / mirrors
  ap_blocks_match_count:       assert property (blocks_DATA_Phy == block_count);
  ap_timeout_value_mirrors:    assert property (timeout_value_DATA_Phy == timeout_counter);

  // Timeout counter behavior
  ap_timeout_inc: assert property (timeout_enable && (timeout_counter < timeout_Reg_Regs_DATA)
                                   |=> timeout_enable && timeout_counter == $past(timeout_counter)+16'd1 && !timeout_Phy_DATA);
  ap_timeout_fire: assert property (timeout_enable && (timeout_counter >= timeout_Reg_Regs_DATA)
                                   |=> !timeout_enable && timeout_counter==16'd0 && timeout_Phy_DATA);
  ap_timeout_rise_cause: assert property ($rose(timeout_Phy_DATA)
                                         |-> $past(timeout_enable) && ($past(timeout_counter) >= $past(timeout_Reg_Regs_DATA)));

  // Start of transfer latching
  sequence start_cond;
    new_DAT_DMA_DATA && serial_Ready_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA;
  endsequence
  ap_start_latch: assert property (start_cond
                                   |=> timeout_counter==16'd0 &&
                                       timeout_enable == $past(timeout_Enable_Regs_DATA) &&
                                       write_read    == $past(writeRead_Regs_DATA) &&
                                       block_count   == $past(blockCount_Regs_DATA) &&
                                       multiple_data == $past(multipleData_Regs_DATA) &&
                                       writeReadPhysical_DATA_Phy == $past(writeRead_Regs_DATA) &&
                                       blocks_DATA_Phy            == $past(blockCount_Regs_DATA) &&
                                       !idle_out_DATA_Phy && strobe_OUT_DATA_Phy && multiple_DATA_Phy);

  // ACK handling (non-last vs last block)
  ap_ack_decrement: assert property (ack_IN_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA && (block_count != 4'd0)
                                     |=> block_count == $past(block_count)-4'd1 &&
                                         blocks_DATA_Phy == $past(block_count)-4'd1 &&
                                         strobe_OUT_DATA_Phy && !multiple_DATA_Phy);
  ap_ack_complete:  assert property (ack_IN_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA && (block_count == 4'd0)
                                     |=> transfer_complete_DATA_DMA && idle_out_DATA_Phy && !multiple_DATA_Phy);

  // Completion signaling
  ap_complete_follows_tc: assert property (transfer_complete_DATA_DMA |-> complete_Phy_DATA);
  ap_complete_rise_cause: assert property ($rose(complete_Phy_DATA) |-> transfer_complete_DATA_DMA);

  // Gating of strobes and acks
  ap_strobe_rise_gated: assert property ($rose(strobe_OUT_DATA_Phy)
                                         |-> (!timeout_enable && !transfer_complete_DATA_DMA) &&
                                             ((new_DAT_DMA_DATA && serial_Ready_Phy_DATA) ||
                                              (ack_IN_Phy_DATA && (block_count != 4'd0))));
  ap_ackout_rise_gated: assert property ($rose(ack_OUT_DATA_Phy)
                                         |-> fifo_OK_FIFO_DATA && !timeout_enable && !transfer_complete_DATA_DMA);

  // Only change writeReadPhysical on start, and to programmed value
  ap_wrp_change_only_on_start: assert property ($changed(writeReadPhysical_DATA_Phy)
                                               |-> start_cond && (writeReadPhysical_DATA_Phy == writeRead_Regs_DATA));

  // Idle and multiple flag transitions
  ap_idle_fall_on_start: assert property ($fell(idle_out_DATA_Phy) |-> start_cond);
  ap_idle_rise_on_last:  assert property ($rose(idle_out_DATA_Phy)
                                          |-> ack_IN_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA && (block_count==4'd0));
  ap_mult_rise_start:    assert property ($rose(multiple_DATA_Phy) |-> start_cond);
  ap_mult_fall_ack:      assert property ($fell(multiple_DATA_Phy)
                                          |-> ack_IN_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA);

  // Coverage
  cv_start:           cover property (start_cond);
  cv_ack_decr:        cover property (ack_IN_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA && (block_count != 4'd0));
  cv_ack_complete:    cover property (ack_IN_Phy_DATA && !timeout_enable && !transfer_complete_DATA_DMA && (block_count == 4'd0));
  cv_timeout_event:   cover property (timeout_enable && (timeout_counter >= timeout_Reg_Regs_DATA));
  cv_ackout_rise:     cover property ($rose(ack_OUT_DATA_Phy));
  cv_strobe_start:    cover property ($rose(strobe_OUT_DATA_Phy) && (new_DAT_DMA_DATA && serial_Ready_Phy_DATA));
  cv_strobe_ack:      cover property ($rose(strobe_OUT_DATA_Phy) && ack_IN_Phy_DATA && (block_count != 4'd0));
  cv_wrp_0:           cover property (start_cond && (writeRead_Regs_DATA==1'b0) ##1 (writeReadPhysical_DATA_Phy==1'b0));
  cv_wrp_1:           cover property (start_cond && (writeRead_Regs_DATA==1'b1) ##1 (writeReadPhysical_DATA_Phy==1'b1));
  cv_zero_blocks:     cover property (start_cond && (blockCount_Regs_DATA==4'd0));
endmodule

bind data_transfer data_transfer_sva sva_inst();