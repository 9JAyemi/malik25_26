// SVA for dff_64: async active-low reset, posedge clocked DFF
// Bind this checker to the DUT instance.

module dff_64_sva (input clk, rst, input [63:0] d, input [63:0] q);

  // Basic sanity
  a_rst_known:       assert property (@(posedge clk) !$isunknown(rst));
  a_q_no_x_when_up:  assert property (@(posedge clk) rst |-> !$isunknown(q));

  // Asynchronous reset must clear q immediately (after NBA)
  a_async_clear:     assert property (@(negedge rst) ##0 (q == 64'h0));

  // While in reset, q must remain 0 (sampled on clk)
  a_hold_zero_in_rst: assert property (@(posedge clk) !rst |-> (q == 64'h0));

  // Functional capture when out of reset: classic 1-cycle pipeline check
  a_capture_pipeline: assert property (@(posedge clk)
                                       (rst && $past(rst)) |-> (q == $past(d)));

  // First cycle after deassertion captures current d on that clock
  a_first_after_deassert: assert property (@(posedge clk) $rose(rst) |-> ##0 (q == d));

  // Optional: stability during reset on clock edges
  a_stable_in_rst:   assert property (@(posedge clk) !rst |-> $stable(q));

  // Coverage
  c_reset_pulse:     cover property (@(negedge rst) 1);
  c_deassert_then_capture:
                     cover property (@(posedge clk) $rose(rst) ##0 (q == d));
  c_data_transfer:   cover property (@(posedge clk)
                                     disable iff (!rst)
                                     ($past(rst) && (d != $past(d))) ##1 (q == $past(d)));

endmodule

// Example bind (instantiate per DUT instance)
// bind dff_64 dff_64_sva u_dff_64_sva (.clk(clk), .rst(rst), .d(d), .q(q));