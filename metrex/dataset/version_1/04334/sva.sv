// SVA for up_counter: concise, high-quality checks and coverage
module up_counter_sva (input logic clk, input logic reset, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  logic past_valid, seen_reset;
  initial begin past_valid = 1'b0; seen_reset = 1'b0; end
  always @(posedge clk) begin
    past_valid <= 1'b1;
    if (reset) seen_reset <= 1'b1;
  end

  // Reset drives zero on every reset cycle
  assert property (reset |-> count == 4'd0);

  // Count is known once we've seen at least one reset pulse
  assert property (disable iff (!past_valid || !seen_reset)
                   !$isunknown(count));

  // Increment by 1 mod 16 on every non-reset cycle (incl. first after reset)
  assert property (disable iff (reset || !past_valid || !seen_reset)
                   count == (($past(count) + 5'd1) & 5'h0F));

  // First non-reset cycle after a reset must be 1
  assert property (disable iff (!past_valid || !seen_reset)
                   (!reset && $past(reset)) |-> count == 4'd1);

  // Explicit wrap check: 15 -> 0 when not in reset
  assert property (disable iff (reset || !past_valid || !seen_reset)
                   $past(count) == 4'd15 |-> count == 4'd0);

  // Stable while reset held across consecutive cycles
  assert property (reset && $past(reset,1,1'b0) |-> $stable(count));

  // Coverage: see reset, leave reset and start counting, and observe wrap
  cover property (reset);
  cover property (reset ##1 (!reset && count == 4'd1) ##1 (!reset && count == 4'd2));
  cover property (disable iff (reset) (count == 4'd15) ##1 (!reset && count == 4'd0));

endmodule

bind up_counter up_counter_sva u_up_counter_sva(.clk(clk), .reset(reset), .count(count));