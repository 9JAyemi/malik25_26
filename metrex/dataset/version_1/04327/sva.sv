// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Establish a valid past sample
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: no X/Z on key signals after first cycle
  assert property (past_valid |-> !$isunknown({reset, enable, count}));

  // Reset behavior: next-cycle clear and hold-at-zero while held
  assert property (reset |=> count == 4'd0);
  assert property (reset [*1:$] |=> (count == 4'd0)[*1:$]);

  // Functional next-state behavior (disabled during reset / first cycle)
  assert property (disable iff (!past_valid || reset)
                   enable |=> count == $past(count) + 4'd1);

  assert property (disable iff (!past_valid || reset)
                   !enable |=> count == $past(count));

  // Optional: after deasserting reset, count is 0 that cycle
  assert property (past_valid && !reset && $past(reset) |-> count == 4'd0);

  // Coverage
  // - Observe at least one increment
  cover property (past_valid && !$past(reset) && $past(enable) ##1
                  count == $past(count)+4'd1);

  // - Observe a hold (no increment) when enable=0
  cover property (past_valid && !$past(reset) && !$past(enable) ##1
                  count == $past(count));

  // - Observe wrap-around from 0xF to 0x0 on increment
  cover property (past_valid && !$past(reset) && $past(enable) &&
                  $past(count)==4'hF ##1 count==4'h0);
endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .count(count)
);