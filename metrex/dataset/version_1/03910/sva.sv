// SVA for counter
module counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [15:0] count
);
  default clocking @(posedge clk); endclocking

  // No X/Z on count after the first sampled cycle
  a_known_count: assert property ( $past(1'b1) |-> !$isunknown(count) );

  // Synchronous reset drives count to zero in the same cycle
  a_reset_zero:  assert property ( reset |-> ##0 (count == 16'd0) );

  // While reset is held, count stays at zero
  a_reset_hold:  assert property ( $past(1'b1) && reset && $past(reset) |-> count == 16'd0 );

  // Increment on consecutive non-reset cycles (non-wrap case)
  a_inc:         assert property ( $past(1'b1) && !reset && !$past(reset) && $past(count) != 16'hFFFF
                                   |-> count == $past(count) + 16'd1 );

  // Wrap-around from 0xFFFF to 0x0000 on next non-reset cycle
  a_wrap:        assert property ( $past(1'b1) && !reset && !$past(reset) && $past(count) == 16'hFFFF
                                   |-> count == 16'h0000 );

  // First cycle after coming out of reset yields 1
  a_post_reset:  assert property ( $past(1'b1) && $past(reset) && !reset |-> count == 16'd1 );

  // Coverage
  c_reset: cover property ( reset ##0 (count == 16'd0) );
  c_rel:   cover property ( $past(1'b1) && $past(reset) && !reset && count == 16'd1 );
  c_wrap:  cover property ( $past(1'b1) && !reset && !$past(reset) && $past(count) == 16'hFFFF && count == 16'h0000 );
endmodule

bind counter counter_sva i_counter_sva(.clk(clk), .reset(reset), .count(count));