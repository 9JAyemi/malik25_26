// SVA for counter
// Binds to the DUT and checks reset, up/down behavior (including wrap), progress, and X-propagation.
// Includes concise functional coverage for both directions and wrap events.

module counter_sva (
  input logic       clk,
  input logic       rst,
  input logic       up_down,
  input logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior: synchronous, count held at 0 while rst asserted
  a_rst_sync:    assert property (rst |-> (count == 4'h0));

  // Counting semantics (use $past() to reference the cycle driving the update)
  a_up_inc:      assert property ($past(!rst) && $past(up_down)==1'b0 && $past(count)!=4'hF |-> count == $past(count)+1);
  a_up_wrap:     assert property ($past(!rst) && $past(up_down)==1'b0 && $past(count)==4'hF |-> count == 4'h0);

  a_down_dec:    assert property ($past(!rst) && $past(up_down)==1'b1 && $past(count)!=4'h0 |-> count == $past(count)-1);
  a_down_wrap:   assert property ($past(!rst) && $past(up_down)==1'b1 && $past(count)==4'h0 |-> count == 4'hF);

  // Always makes progress when not in reset (no hold state)
  a_progress:    assert property ($past(!rst) |-> count != $past(count));

  // No X/Z on key IOs during operation
  a_known_io:    assert property (!rst |-> !$isunknown({up_down, count}));

  // Functional coverage
  c_seen_reset:  cover  property (rst ##1 !rst);
  c_up_nonwrap:  cover  property ($past(!rst) && $past(up_down)==1'b0 && $past(count) inside {[4'h0:4'hE]} && count == $past(count)+1);
  c_down_nonwrap:cover  property ($past(!rst) && $past(up_down)==1'b1 && $past(count) inside {[4'h1:4'hF]} && count == $past(count)-1);
  c_up_wrap:     cover  property ($past(!rst) && $past(up_down)==1'b0 && $past(count)==4'hF && count==4'h0);
  c_down_wrap:   cover  property ($past(!rst) && $past(up_down)==1'b1 && $past(count)==4'h0 && count==4'hF);
  c_dir_change:  cover  property (!rst && up_down==0 ##1 !rst && up_down==1);

endmodule

// Bind into the DUT
bind counter counter_sva i_counter_sva (.clk(clk), .rst(rst), .up_down(up_down), .count(count));