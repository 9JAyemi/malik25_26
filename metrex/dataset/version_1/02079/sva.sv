// SVA for binary_counter. Bind this to the DUT.
// Focused, high-quality checks + meaningful coverage.

module binary_counter_sva (
  input logic        clk,
  input logic        rst,      // active-low async reset
  input logic        up_down,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X/Z on sampled signals (at clock edge)
  a_no_x_inputs:  assert property (!$isunknown({rst, up_down}));
  a_no_x_count:   assert property (!$isunknown(count));

  // Reset behavior: while rst is low, count is held at 0 on every clock
  a_reset_hold:   assert property (!rst |-> count == 4'h0);

  // First functional update right after reset release (synchronous release)
  a_first_update: assert property ($rose(rst) |=> count == (up_down ? 4'd1 : 4'hF));

  // Functional step each enabled cycle (one-step up or down)
  a_inc_step:     assert property (disable iff (!rst || !$past(rst))
                                   up_down |=> count == $past(count) + 4'd1);
  a_dec_step:     assert property (disable iff (!rst || !$past(rst))
                                   !up_down |=> count == $past(count) - 4'd1);

  // Wrap-around corner cases
  a_wrap_up:      assert property (disable iff (!rst || !$past(rst))
                                   (up_down && $past(count)==4'hF) |=> count==4'h0);
  a_wrap_down:    assert property (disable iff (!rst || !$past(rst))
                                   (!up_down && $past(count)==4'h0) |=> count==4'hF);

  // Counter must change every enabled cycle
  a_changes:      assert property (disable iff (!rst || !$past(rst))
                                   count != $past(count));

  // Coverage: reset assertion/deassertion
  c_rst_assert:   cover property ($fell(rst));
  c_rst_release:  cover property ($rose(rst));

  // Coverage: both directions exercised and wrap events seen
  c_inc_seen:     cover property (disable iff (!rst) up_down);
  c_dec_seen:     cover property (disable iff (!rst) !up_down);
  c_wrap_up:      cover property (disable iff (!rst)
                                   (up_down && $past(count)==4'hF) |=> count==4'h0);
  c_wrap_down:    cover property (disable iff (!rst)
                                   (!up_down && $past(count)==4'h0) |=> count==4'hF);

  // Coverage: direction toggle with correct consecutive updates
  c_dir_toggle:   cover property (disable iff (!rst || !$past(rst))
                                   up_down ##1 !up_down);
  c_dir_toggle2:  cover property (disable iff (!rst || !$past(rst))
                                   !up_down ##1 up_down);
endmodule

bind binary_counter binary_counter_sva i_binary_counter_sva (
  .clk(clk), .rst(rst), .up_down(up_down), .count(count)
);