// SVA for up_down_counter
module up_down_counter_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset clears all flops (checked in-cycle)
  a_reset_clears: assert property (rst |-> (count==3'd0 && count_reg1==3'd0 && count_reg2==3'd0));

  // Disable the rest during reset
  default disable iff (rst);

  // No X on output when not in reset
  a_no_x_count: assert property (!$isunknown(count));

  // Pipeline registers follow one-cycle later
  a_cr1_follows_count: assert property (1'b1 |-> ##1 (count_reg1 == $past(count)));
  a_cr2_follows_cr1:   assert property (1'b1 |-> ##1 (count_reg2 == $past(count_reg1)));

  // Datapath: count updates from prior count_reg2 per up_down
  a_count_updates_from_cr2: assert property (1'b1 |-> ##1
    (count == ($past(up_down) ? ($past(count_reg2)+3'd1) : ($past(count_reg2)-3'd1))));

  // Spec-level behavior: 2-cycle relation to count (when out of reset for 2 cycles)
  a_two_cycle_relation: assert property
    ((!$past(rst) && !$past(rst,2)) |-> ##1
      (count == (up_down ? ($past(count,2)+3'd1) : ($past(count,2)-3'd1))));

  // Corner wrap coverages
  c_wrap_up:   cover property ((!$past(rst) && !$past(rst,2)) ##1 (up_down && ($past(count,2)==3'd7) && (count==3'd0)));
  c_wrap_down: cover property ((!$past(rst) && !$past(rst,2)) ##1 (!up_down && ($past(count,2)==3'd0) && (count==3'd7)));

  // Direction seen both ways
  c_both_dirs: cover property (up_down ##[1:$] !up_down);
endmodule

bind up_down_counter up_down_counter_sva sva();