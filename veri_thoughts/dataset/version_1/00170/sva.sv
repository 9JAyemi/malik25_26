bind counter counter_sva i_counter_sva (.*);

module counter_sva (
  input logic        clk, rst, enable, count_dir, dual_count,
  input logic [7:0]  count_out
);

  // Async reset: immediately to 0 and hold at 0 while rst=0
  ap_async_reset_now: assert property (@(negedge rst) ##0 (count_out == 8'h00));
  ap_hold_in_reset:   assert property (@(posedge clk) !rst |-> (count_out == 8'h00 && $stable(count_out)));

  // No X/Z after reset released
  ap_no_xz: assert property (@(posedge clk) disable iff (!rst) !$isunknown(count_out));

  // One-cycle next-state functional correctness (matches DUT precedence and wrap semantics)
  ap_next_state: assert property (@(posedge clk) disable iff (!rst)
    1'b1 |=> count_out ==
      ( $past(enable)
        ? ( ($past(count_dir) == 1'b0 && $past(count_out) == 8'hFF) ? 8'h00 :
            ($past(count_dir) == 1'b1 && $past(count_out) == 8'h00) ? 8'hFF :
            ( $past(count_dir)
              ? ($past(count_out) - ($past(dual_count) ? 8'h02 : 8'h01))
              : ($past(count_out) + ($past(dual_count) ? 8'h02 : 8'h01)) ) )
        : $past(count_out) )
  );

  // Coverage
  cv_hold_when_disabled: cover property (@(posedge clk) disable iff (!rst)
    !$past(enable) ##1 count_out == $past(count_out));

  cv_up_by1:  cover property (@(posedge clk) disable iff (!rst)
    $past(enable) && !$past(count_dir) && !$past(dual_count) && ($past(count_out) != 8'hFF)
    ##1 count_out == ($past(count_out) + 8'h01));

  cv_up_by2:  cover property (@(posedge clk) disable iff (!rst)
    $past(enable) && !$past(count_dir) &&  $past(dual_count) && ($past(count_out) != 8'hFF)
    ##1 count_out == ($past(count_out) + 8'h02));

  cv_down_by1: cover property (@(posedge clk) disable iff (!rst)
    $past(enable) &&  $past(count_dir) && !$past(dual_count) && ($past(count_out) != 8'h00)
    ##1 count_out == ($past(count_out) - 8'h01));

  cv_down_by2: cover property (@(posedge clk) disable iff (!rst)
    $past(enable) &&  $past(count_dir) &&  $past(dual_count) && ($past(count_out) != 8'h00)
    ##1 count_out == ($past(count_out) - 8'h02));

  cv_wrap_up: cover property (@(posedge clk) disable iff (!rst)
    $past(enable) && !$past(count_dir) && ($past(count_out) == 8'hFF)
    ##1 count_out == 8'h00);

  cv_wrap_down: cover property (@(posedge clk) disable iff (!rst)
    $past(enable) &&  $past(count_dir) && ($past(count_out) == 8'h00)
    ##1 count_out == 8'hFF);

  cv_dir_toggle:  cover property (@(posedge clk) disable iff (!rst) $rose(count_dir) && $past(enable));
  cv_step_toggle: cover property (@(posedge clk) disable iff (!rst) $rose(dual_count) && $past(enable));

endmodule