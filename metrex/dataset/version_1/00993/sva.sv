// SVA for binary_counter
// Concise checks for reset, increment, wrap, X-free; plus key coverage.

module binary_counter_sva(
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Guard for $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // No X/Z on count once we have a past sample
  a_no_x:            assert property (past_valid |-> !$isunknown(count));

  // Synchronous reset drives 0 on the next cycle
  a_reset_next0:     assert property (reset |=> (count == 4'd0));

  // If reset is held across cycles, count remains 0
  a_reset_holds0:    assert property (reset && $past(reset) |-> (count == 4'd0));

  // When consecutive cycles are not in reset, counter steps by +1 mod-16
  a_step_mod16:      assert property (past_valid && $past(!reset) && !reset
                                      |-> (count == ($past(count) + 4'd1)));

  // Coverage: observe a full 0..15..0 cycle after reset deassertion
  c_full_cycle: cover property (
      $fell(reset) ##1
      count==4'd0 ##1 count==4'd1 ##1 count==4'd2 ##1 count==4'd3 ##1
      count==4'd4 ##1 count==4'd5 ##1 count==4'd6 ##1 count==4'd7 ##1
      count==4'd8 ##1 count==4'd9 ##1 count==4'd10 ##1 count==4'd11 ##1
      count==4'd12 ##1 count==4'd13 ##1 count==4'd14 ##1 count==4'd15 ##1
      count==4'd0
  );

  // Coverage: explicit wrap event (15 -> 0) with no reset interference
  c_wrap: cover property (past_valid && $past(!reset) && $past(count)==4'd15 ##1 count==4'd0);

endmodule

// Bind to DUT
bind binary_counter binary_counter_sva sva_i(.clk(clk), .reset(reset), .count(count));