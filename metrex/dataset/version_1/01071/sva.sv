// SVA for binary_counter
module binary_counter_sva(input clk, input reset, input [3:0] q);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  ap_reset_hold:        assert property ( !reset |-> q == 4'd0 );
  ap_enter_reset_zero:  assert property ( $fell(reset) |-> q == 4'd0 );

  // Release behavior: first enabled cycle sees 0, then increments if still enabled
  ap_release_start:     assert property ( $rose(reset) |-> (q == 4'd0) and (reset |=> q == 4'd1) );

  // Normal counting (+1 modulo 16) when enabled on consecutive cycles
  ap_count_inc:         assert property ( reset && $past(reset) |-> q == $past(q) + 4'd1 );

  // Sanity: no X/Z when enabled
  ap_no_x_when_en:      assert property ( reset |-> !$isunknown(q) );

  // Coverage
  cp_reset_fall:        cover property ( $fell(reset) );
  cp_reset_rise:        cover property ( $rose(reset) );
  cp_wrap:              cover property ( reset && $past(reset) && $past(q) == 4'hF && q == 4'h0 );
endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (.clk(clk), .reset(reset), .q(q));