// SVA for counter; bind as needed:
// bind counter counter_sva u_counter_sva (.clk(clk), .reset(reset), .enable(enable), .count(count));

module counter_sva (
  input clk,
  input reset,       // active-low synchronous reset
  input enable,
  input [3:0] count
);
  default clocking @(posedge clk); endclocking

  // Basic sanity
  a_no_x:                assert property (!$isunknown({reset, enable, count}));

  // Reset behavior (active-low)
  a_rst_to_zero:         assert property (!reset |=> count == 4'd0);
  a_rst_hold_zero:       assert property (!reset && $past(!reset) |-> (count == 4'd0 && $stable(count)));

  // Counting behavior when not in reset
  a_incr_on_enable:      assert property (reset && enable  |=> count == $past(count) + 4'd1);
  a_hold_when_disabled:  assert property (reset && !enable |=> count == $past(count));

  // No spurious changes: if reset was high and remains high, any change must be due to enable
  a_change_only_if_en:   assert property (reset && $past(reset) && (count != $past(count)) |-> $past(enable));

  // Functional coverage
  c_seen_reset:          cover  property (!reset ##1 reset);
  c_increment:           cover  property (reset && enable ##1 (count == $past(count) + 4'd1));
  c_hold:                cover  property (reset && !enable ##1 (count == $past(count)) ##1 !enable ##1 (count == $past(count)));
  c_wraparound:          cover  property (reset && $past(reset) && $past(enable) && $past(count) == 4'hF ##1 count == 4'h0);
  c_en_pulse_effect:     cover  property (reset && $rose(enable) ##1 (count == $past(count) + 4'd1));
endmodule