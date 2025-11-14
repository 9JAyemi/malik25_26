// SVA for watchdog_timer
`ifndef SYNTHESIS
bind watchdog_timer watchdog_timer_sva watchdog_timer_sva_i();

module watchdog_timer_sva;

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_values: assert property (rst |-> (counter == 32'd0 && t == 1'b0));

  // Counter increments by 1 every active cycle (wraps naturally)
  a_counter_inc:  assert property (disable iff (rst)
                                   $past(1'b1) |-> counter == $past(counter) + 32'd1);

  // t reflects prior-cycle compare of counter vs current timeout
  a_t_def:        assert property (disable iff (rst)
                                   $past(1'b1) |-> (t == ($past(counter) == timeout)));

  // t is a single-cycle pulse
  a_t_pulse:      assert property (disable iff (rst) t |-> ##1 !t);

  // No X/Z on key signals when active
  a_no_x:         assert property (disable iff (rst) (!$isunknown(counter) && !$isunknown(t)));

  // Coverage
  c_timeout_pulse:       cover property (disable iff (rst) $rose(t));
  c_wraparound:          cover property (disable iff (rst)
                                         $past(1'b1) && $past(counter)==32'hFFFF_FFFF && counter==32'h00000000);
  c_timeout_zero_after_reset: cover property (rst ##1 (!rst && timeout==32'd0) ##1 t);

endmodule
`endif