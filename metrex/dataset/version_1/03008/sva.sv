// SVA for binary_search
// Bind into the DUT to see internal regs
bind binary_search bs_sva();

module bs_sva;

  // Use DUT scope names directly (bound inside binary_search)
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // Basic reset sanitation
  ap_reset_regs_clr: assert property (@(posedge clk) !reset |-> ##1 (low==0 && high==0 && mid==0 && i==0 && done==0));
  ap_known_after_reset: assert property (@(posedge clk) reset |-> !$isunknown({found,index,low,high,mid,i,done}));

  // Start must be a 1-cycle pulse when not done
  ap_start_is_pulse: assert property ($rose(start) && !done |=> !start);

  // Start initialization
  ap_start_init: assert property ($rose(start) && !done |=> (low==0 && high==array_len-1 && i==0 && done==0));

  // Iteration step: mid computed from previous low/high; i increments by 1
  ap_mid_calc: assert property ($past(i < array_len && !done) |-> (mid == (($past(low)+$past(high))/32'd2)) && (i == $past(i)+1));

  // Mid stays within [low,high] when bounds are ordered
  ap_mid_in_range: assert property ($past(i < array_len && !done && $past(low) <= $past(high)) |-> (mid >= $past(low) && mid <= $past(high)));

  // Branch: equal -> done, found, index from prior mid
  ap_eq_branch: assert property ((i < array_len && !done && array[mid] == target) |=> (done && found && index == $past(mid)[7:0]));

  // Branch: greater-than -> high reduces, low holds, still not done
  ap_gt_branch: assert property ((i < array_len && !done && array[mid] > target)
                                 |=> (high == $past(mid)-1 && low == $past(low) && !done));

  // Branch: less-than -> low increases, high holds, still not done
  ap_lt_branch: assert property ((i < array_len && !done && array[mid] < target)
                                 |=> (low == $past(mid)+1 && high == $past(high) && !done));

  // Bounds sanity while active
  ap_bounds_low: assert property (!done |-> (low <= {24'b0,array_len})); // allow low==array_len
  ap_bounds_high: assert property (!done && (array_len!=0) |-> (high < {24'b0,array_len}));

  // Termination on i hitting array_len
  ap_terminate_when_i_done: assert property ((i >= array_len && !done) |=> (done && !found && index == 8'hFF));

  // Once done, results and state are sticky until reset
  ap_done_sticky: assert property (done |=> done);
  ap_state_stable_after_done: assert property (done |-> $stable({found,index,low,high,mid,i}));

  // If found, index must be within array_len
  ap_found_index_in_range: assert property (done && found |-> (index < array_len));

  // Coverage
  cp_start_to_done: cover property ($rose(start) && !done ##[1:$] done);
  cp_found_path:    cover property ($rose(start) ##[1:$] (i < array_len && !done && array[mid]==target) ##1 done && found);
  cp_not_found:     cover property ($rose(start) ##[1:$] (i >= array_len && !done) ##1 done && !found);
  cp_go_left:       cover property ($rose(start) ##[1:$] (i < array_len && !done && array[mid] > target));
  cp_go_right:      cover property ($rose(start) ##[1:$] (i < array_len && !done && array[mid] < target));
  cp_zero_len:      cover property ($rose(start) && (array_len==0) ##1 (i >= array_len && !done) ##1 done && !found);

endmodule