// SVA for counter: concise, high-quality checks and coverage
module counter_sva (input clk, input rst, input [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Basic X checks
  a_no_x_rst:   assert property (!$isunknown(rst));
  a_no_x_cnt_on_reset_seen: assert property ((rst || $past(rst)) |-> !$isunknown(count));

  // Synchronous reset drives 0 next sample and holds while asserted
  a_reset_to_zero: assert property (rst |=> (count == 4'd0));
  a_hold_zero_while_reset: assert property (rst && $past(rst) |-> (count == 4'd0 && $stable(count)));

  // Increment by +1 on every non-reset cycle (wraps naturally mod-16)
  a_inc_when_running: assert property (!$isunknown($past(count)) && !rst |=> (count == $past(count) + 4'd1));

  // Optional explicit wrap boundary check (redundant with +1, but clarifies intent)
  a_wrap: assert property (!rst && $past(count)==4'hF |=> count==4'h0);

  // Coverage
  c_reset_pulse: cover property ($rose(rst));
  c_run_no_reset_16: cover property (!rst [*16]); // 16-cycle free run window
  c_wrap_seen: cover property (!rst ##[0:$] (count==4'hF) ##1 (count==4'h0));

endmodule

// Bind into DUT
bind counter counter_sva u_counter_sva (.clk(clk), .rst(rst), .count(count));