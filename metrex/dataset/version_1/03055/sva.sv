// SVA for up_down_counter_4bit
module up_down_counter_4bit_sva (input clk, input Up, input Down, input [3:0] Q);

  default clocking cb @(posedge clk); endclocking

  logic past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // No X/Z after first sampled cycle
  assert property (past_valid |-> !$isunknown({Up, Down, Q}));

  // Priority and next-state behavior
  // Up takes priority over Down
  assert property (past_valid && $past(Up)
                   |-> Q == (($past(Q)==4'hF) ? 4'h0 : $past(Q)+1));

  // Down only when Up was not asserted
  assert property (past_valid && !$past(Up) && $past(Down)
                   |-> Q == (($past(Q)==4'h0) ? 4'hF : $past(Q)-1));

  // Hold when neither asserted
  assert property (past_valid && !$past(Up) && !$past(Down)
                   |-> Q == $past(Q));

  // Optional safety: if Q changed, it must be a legal step (+1/-1 with wrap)
  assert property (past_valid && (Q != $past(Q))
                   |-> ((Q == $past(Q)+1) || (Q == $past(Q)-1) ||
                        ($past(Q)==4'hF && Q==4'h0) ||
                        ($past(Q)==4'h0 && Q==4'hF)));

  // Functional coverage
  // Increment (non-wrap)
  cover property (past_valid && $past(Up) && ($past(Q)!=4'hF) && (Q==$past(Q)+1));
  // Increment wrap 15->0
  cover property (past_valid && $past(Up) && ($past(Q)==4'hF) && (Q==4'h0));
  // Decrement (non-wrap)
  cover property (past_valid && !$past(Up) && $past(Down) && ($past(Q)!=4'h0) && (Q==$past(Q)-1));
  // Decrement wrap 0->15
  cover property (past_valid && !$past(Up) && $past(Down) && ($past(Q)==4'h0) && (Q==4'hF));
  // Hold
  cover property (past_valid && !$past(Up) && !$past(Down) && (Q==$past(Q)));
  // Both Up and Down high -> Up wins (increment or wrap)
  cover property (past_valid && $past(Up && Down) &&
                  (Q == (($past(Q)==4'hF) ? 4'h0 : $past(Q)+1)));

endmodule

bind up_down_counter_4bit up_down_counter_4bit_sva u_up_down_counter_4bit_sva (.*);