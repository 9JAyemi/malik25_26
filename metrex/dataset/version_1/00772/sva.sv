// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Track valid past-sample
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset behavior
  a_reset_clears_next: assert property (reset |=> count == 4'd0);
  a_reset_holds_zero:  assert property (past_valid && $past(reset) |-> count == 4'd0);

  // Next-state function when not in reset
  a_wrap_at_9: assert property (past_valid && !reset && $past(!reset) && ($past(count) == 4'd9) |-> count == 4'd0);
  a_inc_else:  assert property (past_valid && !reset && $past(!reset) && ($past(count) != 4'd9) |-> count == $past(count) + 4'd1);

  // Legal state and no-X while not in reset
  a_range_0_to_9: assert property (disable iff (reset) count <= 4'd9);
  a_no_xz:        assert property (disable iff (reset) !$isunknown(count));

  // Functional coverage
  c_reset_effect: cover property (reset |=> count == 4'd0);
  c_wrap:         cover property (disable iff (reset) (count == 4'd9 ##1 count == 4'd0));
  sequence s_full_cycle;
    count==4'd0 ##1 count==4'd1 ##1 count==4'd2 ##1 count==4'd3 ##1 count==4'd4
    ##1 count==4'd5 ##1 count==4'd6 ##1 count==4'd7 ##1 count==4'd8 ##1 count==4'd9 ##1 count==4'd0;
  endsequence
  c_full_decade:  cover property (disable iff (reset) s_full_cycle);

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva sva_i (.clk(clk), .reset(reset), .count(count));