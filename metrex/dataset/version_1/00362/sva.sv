// SVA for counter_3bit
module counter_3bit_sva(input clk, input reset, input [2:0] out);

  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on key signals
  a_no_x: assert property ( !$isunknown({reset,out}) );

  // Reset behavior (synchronous, active-high)
  a_reset_clears_next:    assert property ( $rose(reset) |=> out == 3'd0 );
  a_hold_zero_in_reset:   assert property ( reset && $past(reset) |-> out == 3'd0 );
  a_deassert_starts_at_1: assert property ( $fell(reset) |=> out == 3'd1 );

  // Counting when not in reset
  default disable iff (reset);
  a_inc_each_cycle: assert property ( !$past(reset) |-> out == ($past(out)+3'd1) );
  a_wrap_7_to_0:    assert property ( !$past(reset) && $past(out)==3'd7 |-> out==3'd0 );

  // Coverage
  c_after_deassert_counts: cover property ( $fell(reset) ##1 out==3'd1 ##1 out==3'd2 ##1 out==3'd3 );
  c_wrap:                  cover property ( !$past(reset) && $past(out)==3'd7 && out==3'd0 );

endmodule

// Bind into DUT
bind counter_3bit counter_3bit_sva u_counter_3bit_sva(.clk(clk), .reset(reset), .out(out));