// SVA for sync_ptr: concise, high-quality checks and minimal but meaningful coverage

module sync_ptr_sva #(parameter ASIZE = 4) ();
  // Bound into sync_ptr scope; can see dest_clk, dest_rst_n, src_ptr, dest_ptr, ptr_x
  default clocking cb @(posedge dest_clk); endclocking

  // Asynchronous reset holds pipeline at zero and no Xs while low
  a_reset_clears: assert property (!dest_rst_n |-> (dest_ptr == '0 && ptr_x == '0 && !$isunknown({dest_ptr,ptr_x})));

  // No Xs out of reset
  a_no_x: assert property (disable iff (!dest_rst_n) !$isunknown({dest_ptr,ptr_x}));

  // One-cycle pipeline relation for both stages
  a_pipe: assert property (disable iff (!dest_rst_n) 1'b1 |=> {dest_ptr,ptr_x} == $past({ptr_x,src_ptr}));

  // First active cycle after reset release
  a_post_reset: assert property ($rose(dest_rst_n) |=> (dest_ptr == '0 && ptr_x == $past(src_ptr)));

  // End-to-end: if input stable for two cycles, output matches it two cycles later
  a_two_cycle_latency: assert property (disable iff (!dest_rst_n) $stable(src_ptr)[*2] |=> dest_ptr == $past(src_ptr,2));

  // Change causality: dest_ptr changes only if ptr_x changed in the previous cycle
  a_change_causal: assert property (disable iff (!dest_rst_n) $changed(dest_ptr) |-> $past($changed(ptr_x)));

  // Minimal coverage
  c_reset_seq:     cover property ($fell(dest_rst_n) ##1 $rose(dest_rst_n));
  c_dest_activity: cover property (disable iff (!dest_rst_n) $changed(dest_ptr));
  c_end_to_end:    cover property (disable iff (!dest_rst_n) $stable(src_ptr)[*2] ##1 (dest_ptr == $past(src_ptr,2)));
endmodule

bind sync_ptr sync_ptr_sva #(.ASIZE(ASIZE)) u_sync_ptr_sva();