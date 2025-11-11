// SVA for fmlarb_dack
// Bind into DUT to check internal pipeline and masking behavior

module fmlarb_dack_sva;
  default clocking cb @(posedge sys_clk); endclocking

  // Reset clears all state (do not disable on reset for this check)
  a_reset_clears: assert property (disable iff (1'b0)
    sys_rst |=> (!ack && !ack0 && !mask && !ack_read0 && !ack_read1 && !ack_read2)
  );

  // Causality: ack can only be due to a write 2 cycles ago or read 5 cycles ago
  a_ack_cause: assert property (disable iff (sys_rst)
    ack |-> ($past(write,2) || $past(read,5))
  );

  // Latency guarantees on rising edges (allow ack already high)
  a_write_latency: assert property (disable iff (sys_rst)
    $rose(write) |-> ##2 ack
  );
  a_read_latency: assert property (disable iff (sys_rst)
    $rose(read)  |-> ##5 ack
  );

  // Mask state machine: priority clear on ack, set on eack, hold otherwise
  a_ack_clears_mask: assert property (disable iff (sys_rst)
    ack |=> !mask
  );
  a_eack_sets_mask: assert property (disable iff (sys_rst)
    (eack && !ack) |=> mask
  );
  a_mask_holds_no_event: assert property (disable iff (sys_rst)
    (!eack && !ack) |=> $stable(mask)
  );

  // stbm gating
  a_stbm_comb: assert property (disable iff (sys_rst)
    stbm == (stb && !mask)
  );
  a_mask_blocks_stbm: assert property (disable iff (sys_rst)
    mask |-> !stbm
  );
  a_unmasked_passes_stb: assert property (disable iff (sys_rst)
    !mask |-> (stbm == stb)
  );

  // Once eack seen (and no simultaneous ack), block stbm until ack arrives
  a_block_until_ack: assert property (disable iff (sys_rst)
    (eack && !ack) |-> ##1 (!stbm until_with ack)
  );

  // Mutual exclusion of read/write qualifiers
  a_mutual_excl: assert property (disable iff (sys_rst)
    !(read && write)
  );

  // Optional pulse-width checks for isolated one-cycle ops (non-overlapping cases)
  a_write_pulse_width_isolated: assert property (disable iff (sys_rst)
    ($rose(write) ##1 !write) |-> (##2 ack ##1 !ack)
  );
  a_read_pulse_width_isolated: assert property (disable iff (sys_rst)
    ($rose(read)  ##1 !read)  |-> (##5 ack ##1 !ack)
  );

  // Coverage
  c_write_ack:  cover property (disable iff (sys_rst) $rose(write) ##2 ack ##1 !ack);
  c_read_ack:   cover property (disable iff (sys_rst) $rose(read)  ##5 ack ##1 !ack);
  c_eack_ack_same: cover property (disable iff (sys_rst) eack && ack);
  c_back_to_back_writes: cover property (disable iff (sys_rst) $rose(write) ##1 $rose(write) ##2 ack);
  c_mask_lifecycle: cover property (disable iff (sys_rst) $rose(eack) ##1 mask ##[1:$] ack ##1 !mask);
endmodule

bind fmlarb_dack fmlarb_dack_sva sva_i;