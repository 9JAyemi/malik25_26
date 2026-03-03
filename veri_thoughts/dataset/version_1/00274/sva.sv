// SVA for NV_NVDLA_RT_cacc2glb
// Bind into DUT to access internal pipeline regs.

module NV_NVDLA_RT_cacc2glb_sva;

  default clocking cb @(posedge nvdla_core_clk); endclocking
  default disable iff (!nvdla_core_rstn);

  // Reset behavior
  a_reset_clears: assert property (@cb !nvdla_core_rstn |-> 
    (cacc2glb_done_intr_pd_d1==2'b0 && cacc2glb_done_intr_pd_d2==2'b0 && cacc2glb_done_intr_dst_pd==2'b0));

  // Stage relations
  a_d1_follows_src_same_cycle: assert property (@cb
    cacc2glb_done_intr_pd_d1 == cacc2glb_done_intr_src_pd);

  a_d2_follows_d1_one_cycle: assert property (@cb
    $past(nvdla_core_rstn) |-> (cacc2glb_done_intr_pd_d2 == $past(cacc2glb_done_intr_pd_d1)));

  a_dst_equals_d2: assert property (@cb
    cacc2glb_done_intr_dst_pd == cacc2glb_done_intr_pd_d2);

  // End-to-end latency (1-cycle)
  a_end_to_end_1cyc: assert property (@cb
    $past(nvdla_core_rstn) |-> (cacc2glb_done_intr_dst_pd == $past(cacc2glb_done_intr_src_pd)));

  // No X on output when out of reset
  a_no_x_out: assert property (@cb
    !$isunknown(cacc2glb_done_intr_dst_pd));

  // Coverage: edge propagation per bit
  c_bit0_rise: cover property (@cb
    $rose(cacc2glb_done_intr_src_pd[0]) ##1 cacc2glb_done_intr_dst_pd[0]);
  c_bit0_fall: cover property (@cb
    $fell(cacc2glb_done_intr_src_pd[0]) ##1 !cacc2glb_done_intr_dst_pd[0]);

  c_bit1_rise: cover property (@cb
    $rose(cacc2glb_done_intr_src_pd[1]) ##1 cacc2glb_done_intr_dst_pd[1]);
  c_bit1_fall: cover property (@cb
    $fell(cacc2glb_done_intr_src_pd[1]) ##1 !cacc2glb_done_intr_dst_pd[1]);

  // Coverage: any vector change propagates after 1 cycle
  c_vec_change: cover property (@cb
    $changed(cacc2glb_done_intr_src_pd) ##1 (cacc2glb_done_intr_dst_pd == $past(cacc2glb_done_intr_src_pd)));

endmodule

bind NV_NVDLA_RT_cacc2glb NV_NVDLA_RT_cacc2glb_sva u_NV_NVDLA_RT_cacc2glb_sva();