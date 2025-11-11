// SVA for synchronous_counter
module synchronous_counter_sva (input logic clk, input logic reset, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Next-state function check (covers reset behavior, increment, and wrap)
  assert property (past_valid |-> 
                   count == ( $past(reset) ? 4'h0
                                           : ($past(count)==4'hF ? 4'h0 : $past(count)+4'd1)));

  // Progress when not in reset (must change every cycle)
  assert property (past_valid && !$past(reset) |-> count != $past(count));

  // No X/Z after first sampled clock
  assert property (past_valid |-> !$isunknown({reset,count}));

  // Coverage
  cover property (reset); // reset observed
  cover property (past_valid && $past(reset) && !reset ##1 (count==4'd1) ##1 (count==4'd2)); // post-reset 1->2
  cover property (past_valid && !$past(reset) && $past(count)==4'hF && count==4'h0); // wrap 15->0

endmodule

bind synchronous_counter synchronous_counter_sva sva_i (.clk(clk), .reset(reset), .count(count));