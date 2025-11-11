// SVA for dmac_2d_transfer
// Bind into the DUT; uses internal signals directly
bind dmac_2d_transfer dmac_2d_transfer_sva();

module dmac_2d_transfer_sva;

  default clocking cb @(posedge req_aclk); endclocking
  default disable iff (!req_aresetn);

  // Basic passthrough invariants
  a_out_req_dest_addr: assert property (out_req_dest_address == dest_address);
  a_out_req_src_addr:  assert property (out_req_src_address  == src_address);
  a_out_req_len:       assert property (out_req_length       == x_length);

  // Reset values while reset asserted
  a_reset_vals: assert property (disable iff (1'b0)
    (!req_aresetn |-> (req_ready && !out_req_valid && !out_req_sync_transfer_start &&
                       !req_eot && (req_id==2'b00) && (eot_id==2'b00) &&
                       dest_address=='0 && src_address=='0 &&
                       x_length=='0 && y_length=='0 &&
                       dest_stride=='0 && src_stride=='0)));

  // Handshake acceptance loads and state
  a_accept_loads: assert property (
    req_ready && req_valid |->
      ##1 (dest_address===$past(req_dest_address) &&
           src_address ===$past(req_src_address)  &&
           x_length    ===$past(req_x_length)     &&
           y_length    ===$past(req_y_length)     &&
           dest_stride ===$past(req_dest_stride)  &&
           src_stride  ===$past(req_src_stride)   &&
           out_req_sync_transfer_start===$past(req_sync_transfer_start) &&
           out_req_valid && !req_ready));

  // While idle (ready, no valid), registers stay stable
  a_idle_stable: assert property (
    req_ready && !req_valid |->
      ##1 $stable({dest_address,src_address,x_length,y_length,
                   dest_stride,src_stride,out_req_sync_transfer_start,out_req_valid}));

  // While active and blocked, beat regs stay stable
  a_blocked_stable: assert property (
    !req_ready && !(out_req_valid && out_req_ready) |->
      ##1 $stable({dest_address,src_address,x_length,y_length,
                   dest_stride,src_stride,out_req_sync_transfer_start}));

  // Ready/valid exclusivity
  a_ready_no_valid: assert property (req_ready |-> !out_req_valid);
  a_active_valid:   assert property (!req_ready |->  out_req_valid);

  // Per-beat updates on handshake
  a_addr_len_update: assert property (
    out_req_valid && out_req_ready |->
      ##1 (dest_address == $past(dest_address) +
                      $past(dest_stride[C_DMA_LENGTH_WIDTH-1:C_BYTES_PER_BEAT_WIDTH_DEST]) &&
           src_address  == $past(src_address)  +
                      $past(src_stride [C_DMA_LENGTH_WIDTH-1:C_BYTES_PER_BEAT_WIDTH_SRC])  &&
           y_length     == $past(y_length) - 1));

  // out_req_valid/req_ready next-state rules around last beat
  a_last_deasserts: assert property (
    out_req_valid && out_req_ready && (y_length==0) |->
      ##1 (!out_req_valid && req_ready));
  a_mid_stays: assert property (
    out_req_valid && out_req_ready && (y_length!=0) |->
      ##1 ( out_req_valid && !req_ready));

  // Sync-transfer pulse behavior
  a_sync_only_while_active: assert property (out_req_sync_transfer_start |-> out_req_valid && !req_ready);
  a_sync_clears_on_first_beat: assert property (
    out_req_valid && out_req_ready && out_req_sync_transfer_start |->
      ##1 !out_req_sync_transfer_start);

  // ID/EOT bookkeeping
  a_req_id_incr: assert property (
    out_req_valid && out_req_ready |->
      ##1 (req_id == $past(req_id)+1));
  a_last_req_write: assert property (
    out_req_valid && out_req_ready |->
      ##1 (last_req[$past(req_id)] == $past(y_length==0)));
  a_eot_id_incr: assert property (out_eot |->
      ##1 (eot_id == $past(eot_id)+1));
  a_req_eot_only_with_out_eot: assert property (!out_eot |-> !req_eot);
  a_req_eot_value: assert property (out_eot |-> (req_eot == $past(last_req[eot_id])));

  // Covers
  c_singleline: cover property (
    req_ready && req_valid && (req_y_length==0)
    ##1 (out_req_valid && out_req_ready && (y_length==0))
    ##1 (!out_req_valid && req_ready)
    ##[1:5] (out_eot && req_eot));

  c_multiline: cover property (
    req_ready && req_valid && (req_y_length>0)
    ##1 out_req_valid
    ##1 (out_req_valid && out_req_ready && (y_length!=0))
    ##[1:5] (out_req_valid && out_req_ready && (y_length==0))
    ##1 (!out_req_valid && req_ready));

  c_sync_pulse: cover property (
    req_ready && req_valid && req_sync_transfer_start
    ##1 (out_req_valid && out_req_sync_transfer_start)
    ##1 (out_req_valid && out_req_ready)
    ##1 !out_req_sync_transfer_start);

endmodule