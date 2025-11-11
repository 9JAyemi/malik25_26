// SVA for counter
module counter_sva(
  input clk,
  input rst,
  input en,
  input [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior: next cycle must be 0 when rst is 1
  a_reset_next_zero: assert property (rst |=> count == 4'd0);

  // After reset, counter either holds or increments by +1 (with natural 4-bit wrap)
  a_step_or_hold: assert property (
    !$past(rst) |-> ( $past(en) ? (count == ($past(count) + 4'd1)) : (count == $past(count)) )
  );

  // No X/Z on count during normal operation
  a_no_x: assert property (disable iff (rst) !$isunknown(count));

  // Covers
  c_reset_effect: cover property (rst |=> count == 4'd0);
  c_single_inc:   cover property (disable iff (rst) $past(en) && !$past(rst) && (count == ($past(count) + 4'd1)));
  c_hold_seq:     cover property (disable iff (rst) (!en)[*3] ##1 $stable(count));
  c_wraparound:   cover property (disable iff (rst) $past(en) && ($past(count) == 4'hF) && (count == 4'h0));
endmodule

// Bind into DUT
bind counter counter_sva u_counter_sva(.clk(clk), .rst(rst), .en(en), .count(count));