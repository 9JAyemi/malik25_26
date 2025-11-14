// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // helper for safe $past usage
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // No X/Z on observed/control (after first sampled cycle)
  assert property (past_valid |-> !$isunknown(reset));
  assert property (past_valid |-> !$isunknown(count));

  // Synchronous reset drives count to 0 on the next cycle, and is seen the cycle after it was asserted
  assert property (reset |=> count == 4'h0);
  assert property (past_valid && $past(reset) |-> count == 4'h0);

  // Mod-16 increment when not in reset (covers both increment and wrap 15->0)
  assert property (past_valid && !reset |=> count == $past(count) + 4'd1);

  // Zero can only result from prior reset or wrap (when current cycle is not in reset)
  assert property (past_valid && !reset && count == 4'h0 |-> $past(reset) || $past(count) == 4'hF);

  // Coverage: hit all values, wrap, and a reset transition
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : CVALS
      cover property (!reset && count == i[3:0]);
    end
  endgenerate
  cover property (!reset && count == 4'hF ##1 !reset && count == 4'h0);
  cover property (reset ##1 !reset && count == 4'h0);
endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (.clk(clk), .reset(reset), .count(count));