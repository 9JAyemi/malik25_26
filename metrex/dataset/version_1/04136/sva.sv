// SVA for ewrapper_link_txo
// Bind this module to the DUT: bind ewrapper_link_txo ewrapper_link_txo_sva();

module ewrapper_link_txo_sva;

  default clocking cb @(posedge txo_lclk); endclocking
  default disable iff (reset);

  // ========== Reset checks (sampled on next clock) ==========
  // Asynchronous reset drives these low; check they are low after a reset edge
  assert property ($rose(reset) |=> !shadow_access && !txo_emesh_wait && !cycle1_access && !cycle2_access && !byte0_inc0 && (tx_in==72'b0));

  // ========== Shadow/mux path (front-end backpressure) ==========
  // Shadow updates only when not waiting
  assert property (~txo_emesh_wait |=> shadow_access == $past(txo_emesh_access));
  assert property ( txo_emesh_wait |=> shadow_access == $past(shadow_access));
  assert property (~txo_emesh_wait |=> shadow_write  == $past(txo_emesh_write));
  assert property ( txo_emesh_wait |=> shadow_write  == $past(shadow_write));
  assert property (~txo_emesh_wait |=> shadow_datamode == $past(txo_emesh_datamode));
  assert property ( txo_emesh_wait |=> shadow_datamode == $past(shadow_datamode));
  assert property (~txo_emesh_wait |=> shadow_ctrlmode == $past(txo_emesh_ctrlmode));
  assert property ( txo_emesh_wait |=> shadow_ctrlmode == $past(shadow_ctrlmode));
  assert property (~txo_emesh_wait |=> shadow_dstaddr == $past(txo_emesh_dstaddr));
  assert property ( txo_emesh_wait |=> shadow_dstaddr == $past(shadow_dstaddr));
  assert property (~txo_emesh_wait |=> shadow_srcaddr == $past(txo_emesh_srcaddr));
  assert property ( txo_emesh_wait |=> shadow_srcaddr == $past(shadow_srcaddr));
  assert property (~txo_emesh_wait |=> shadow_data    == $past(txo_emesh_data));
  assert property ( txo_emesh_wait |=> shadow_data    == $past(shadow_data));

  // emesh_* muxing vs wait
  assert property ( txo_emesh_wait |-> (emesh_access==shadow_access && emesh_write==shadow_write &&
                                        emesh_datamode==shadow_datamode && emesh_ctrlmode==shadow_ctrlmode &&
                                        emesh_dstaddr==shadow_dstaddr && emesh_srcaddr==shadow_srcaddr &&
                                        emesh_data==shadow_data));
  assert property (!txo_emesh_wait |-> (emesh_access==txo_emesh_access && emesh_write==txo_emesh_write &&
                                        emesh_datamode==txo_emesh_datamode && emesh_ctrlmode==txo_emesh_ctrlmode &&
                                        emesh_dstaddr==txo_emesh_dstaddr && emesh_srcaddr==txo_emesh_srcaddr &&
                                        emesh_data==txo_emesh_data));

  // ========== Wait generation ==========
  assert property (emesh_wait == (cycle1_access & cycle2_access & ~burst_tran));
  assert property (txo_emesh_wait == $past(emesh_wait));

  // ========== Pipeline stage 1 (cycle1_*) ==========
  assert property (~emesh_wait |=> cycle1_access == $past(emesh_access));
  assert property ( emesh_wait |=> cycle1_access == $past(cycle1_access));
  assert property (~emesh_wait |=> cycle1_write      == $past(emesh_write));
  assert property ( emesh_wait |=> cycle1_write      == $past(cycle1_write));
  assert property (~emesh_wait |=> cycle1_datamode   == $past(emesh_datamode));
  assert property ( emesh_wait |=> cycle1_datamode   == $past(cycle1_datamode));
  assert property (~emesh_wait |=> cycle1_ctrlmode   == $past(emesh_ctrlmode));
  assert property ( emesh_wait |=> cycle1_ctrlmode   == $past(cycle1_ctrlmode));
  assert property (~emesh_wait |=> cycle1_dstaddr    == $past(emesh_dstaddr));
  assert property ( emesh_wait |=> cycle1_dstaddr    == $past(cycle1_dstaddr));
  assert property (~emesh_wait |=> cycle1_srcaddr    == $past(emesh_srcaddr));
  assert property ( emesh_wait |=> cycle1_srcaddr    == $past(cycle1_srcaddr));
  assert property (~emesh_wait |=> cycle1_data       == $past(emesh_data));
  assert property ( emesh_wait |=> cycle1_data       == $past(cycle1_data));

  // Derived: double-word detection and +8 address
  assert property (cycle1_dbl == (cycle1_access & cycle1_write & &cycle1_datamode));
  assert property (cycle1_dstaddr_inc8 == (cycle1_dstaddr + 32'd8));

  // ========== Pipeline stage 2 (cycle2_*) ==========
  assert property ( emesh_wait |=> cycle2_access == 1'b0);
  assert property (~emesh_wait |=> cycle2_access == $past(cycle1_access));
  assert property (cycle2_dstaddr      == $past(cycle1_dstaddr));
  assert property (cycle2_srcaddr      == $past(cycle1_srcaddr));
  assert property (cycle2_data         == $past(cycle1_data));
  assert property (cycle2_dbl          == $past(cycle1_dbl));
  assert property (cycle2_dstaddr_inc8 == $past(cycle1_dstaddr_inc8));

  // ========== Burst detection and byte0_inc0 ==========
  assert property (inc8_match == (cycle1_dbl & cycle2_dbl & (cycle1_dstaddr == cycle2_dstaddr_inc8)));
  assert property (inc0_match == (cycle1_dbl & cycle2_dbl & (cycle1_dstaddr == cycle2_dstaddr)));
  assert property (burst_tran == (burst_en & cycle1_dbl & cycle2_dbl &
                                 ((inc8_match & ~byte0_inc0) | (inc0_match & byte0_inc0))));
  // delayed taps
  assert property (cycle1_frame_bit_del == $past(cycle1_frame_bit));
  assert property (inc0_match_del       == $past(inc0_match));
  // update rule for byte0_inc0
  assert property ( cycle1_frame_bit_del |=> byte0_inc0 == $past(inc0_match_del));
  assert property (!cycle1_frame_bit_del |=> byte0_inc0 == $past(byte0_inc0));

  // ========== Framing ==========
  assert property (cycle1_frame_bit == (cycle1_access & ~cycle2_access));
  assert property (cycle2_frame_bit == cycle2_access);
  assert property (cycle1_frame == {2'b00,{6{cycle1_frame_bit}}});
  assert property (cycle2_frame == {8{cycle2_frame_bit}});
  assert property (txo_frame_int == (cycle1_frame | cycle2_frame));

  // ========== Payload construction/select ==========
  // tran_byte0 layout
  assert property (tran_byte0[7]   == ~cycle1_write);
  assert property (tran_byte0[6:3] == 4'b0000);
  assert property (tran_byte0[2]   == byte0_inc0);
  assert property (tran_byte0[1:0] == 2'b00);

  // cycle1_data_long layout
  assert property (cycle1_data_long[63:56] == 8'h00);
  assert property (cycle1_data_long[55:48] == 8'h00);
  assert property (cycle1_data_long[47:40] == tran_byte0);
  assert property (cycle1_data_long[39:36] == cycle1_ctrlmode);
  assert property (cycle1_data_long[35:32] == cycle1_dstaddr[31:28]);
  assert property (cycle1_data_long[31:24] == cycle1_dstaddr[27:20]);
  assert property (cycle1_data_long[23:16] == cycle1_dstaddr[19:12]);
  assert property (cycle1_data_long[15:8]  == cycle1_dstaddr[11:4]);
  assert property (cycle1_data_long[7:4]   == cycle1_dstaddr[3:0]);
  assert property (cycle1_data_long[3:2]   == cycle1_datamode);
  assert property (cycle1_data_long[1]     == cycle1_write);
  assert property (cycle1_data_long[0]     == cycle1_access);

  // cycle2_data_long layout
  assert property (cycle2_data_long[63:32] == cycle2_data);
  assert property (cycle2_data_long[31:0]  == cycle2_srcaddr);

  // data_long selection
  assert property ( cycle2_access |-> data_long == cycle2_data_long);
  assert property (!cycle2_access |-> data_long == cycle1_data_long);

  // ========== Channelization and output packing ==========
  // Sample two channels for mapping correctness
  assert property (channel0 == {data_long[56],data_long[48],data_long[40],data_long[32],data_long[24],data_long[16],data_long[8],data_long[0]});
  assert property (channel7 == {data_long[63],data_long[55],data_long[47],data_long[39],data_long[31],data_long[23],data_long[15],data_long[7]});

  // txo_data_int packing
  assert property (txo_data_int == {txo_frame_int,channel7,channel6,channel5,channel4,channel3,channel2,channel1,channel0});

  // tx_in registered output
  assert property (tx_in == $past(txo_data_int));

  // ========== Sanity (no X on key outputs when not in reset) ==========
  assert property (!$isunknown(txo_emesh_wait));
  assert property (!$isunknown(tx_in));

  // ========== Functional coverage ==========
  // Wait assertion event
  cover property (cycle1_access && cycle2_access && !burst_tran ##1 txo_emesh_wait);

  // Double-word detection
  cover property (cycle1_dbl);

  // Burst on +8 increment path
  cover property (burst_en && cycle1_dbl && cycle2_dbl && inc8_match && !byte0_inc0 && burst_tran);

  // Burst on +0 path (same address)
  cover property (burst_en && cycle1_dbl && cycle2_dbl && inc0_match &&  byte0_inc0 && burst_tran);

  // Byte0_inc0 toggle across frames
  cover property (cycle1_frame_bit_del && $changed(byte0_inc0));

  // Shadow path exercised for multiple cycles while inputs change
  cover property ( txo_emesh_wait [*2] and $changed(txo_emesh_access) );

  // Both datamodes observed: 00 and 11
  cover property (~(&cycle1_datamode));
  cover property ( &cycle1_datamode );

endmodule

bind ewrapper_link_txo ewrapper_link_txo_sva();