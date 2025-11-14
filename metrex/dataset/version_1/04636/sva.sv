// Bindable SVA for binary_counter
module binary_counter_sva(input logic clk, reset, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // No X/Z on count when out of reset
  a_no_x:        assert property (disable iff (reset) !$isunknown(count));

  // While reset is asserted, counter is forced to 0 (and remains 0)
  a_rst_next0:   assert property (reset |-> (count == 4'd0));
  a_rst_hold0:   assert property (reset && $past(reset) |-> (count == 4'd0));

  // First count after reset release is 1 (from 0), assuming reset stays low
  a_first_after_release:
                  assert property ($fell(reset) ##1 (!reset && count == 4'd1));

  // Increment by one modulo-16 when continuously out of reset
  a_inc_mod16:   assert property ((!reset && $past(!reset))
                                  |-> (count == (($past(count) + 1) % 16)));

  // Explicit wrap check F -> 0 (redundant with a_inc_mod16, but clearer)
  a_wrap:        assert property (disable iff (reset)
                                  ($past(count) == 4'hF) |-> (count == 4'h0));

  // Coverage
  c_saw_reset:   cover  property ($rose(reset));
  c_wrap:        cover  property (disable iff (reset) (count == 4'hF) ##1 (count == 4'h0));
  c_full_cycle:  cover  property (disable iff (reset) (count == 4'h0) ##16 (count == 4'h0));

endmodule

// Example bind (uncomment in your environment):
// bind binary_counter binary_counter_sva u_sva (.clk(clk), .reset(reset), .count(count));