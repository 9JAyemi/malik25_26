// SVA for binary_counter. Bind this checker to the DUT.
module binary_counter_sva(input logic clk, reset, input logic [3:0] count);
  default clocking cb @(posedge clk); endclocking

  // Past-valid guard for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Sanity: no X/Z on key signals
  assert property (! $isunknown(reset)) else $error("reset is X/Z");
  assert property (! $isunknown(count)) else $error("count is X/Z");

  // Reset behavior: synchronous reset forces count to 0 in the same cycle
  assert property (reset |-> (count == 4'h0))
    else $error("Count not zero during reset");

  // First cycle after reset deasserts must start at 1
  assert property (past_valid && !reset && $past(reset) |-> (count == 4'h1))
    else $error("Count not 1 right after reset deassert");

  // Normal counting when not in reset (includes wrap via 4-bit truncation)
  assert property (past_valid && !reset && $past(!reset) |-> (count == $past(count) + 4'd1))
    else $error("Count did not increment by 1 when not in reset");

  // Coverage: observe wrap-around and post-reset start
  cover property (past_valid && !reset && $past(!reset) && ($past(count) == 4'hF) ##0 (count == 4'h0));
  cover property (past_valid && !reset && $past(reset) && (count == 4'h1));
endmodule

// Bind to DUT instance(s)
bind binary_counter binary_counter_sva u_binary_counter_sva(.clk(clk), .reset(reset), .count(count));