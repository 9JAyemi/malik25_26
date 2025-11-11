// SVA for counter. Bind this to the DUT.
module counter_sva (
  input logic       clk,
  input logic       areset,
  input logic       enable,
  input logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity (inputs/outputs known)
  assert property (cb !$isunknown({areset, enable}));
  assert property (cb disable iff (areset) !$isunknown(count));

  // Reset behavior: clears next cycle and holds at 0 while asserted
  assert property (cb areset |=> (count == 4'd0));
  assert property (cb (areset && $past(areset)) |-> (count == 4'd0));

  // Functional behavior when not in reset
  // If enable=1, increment by 1 (mod-16); if enable=0, hold
  assert property (cb disable iff (areset)  enable |=> (count == $past(count) + 4'd1));
  assert property (cb disable iff (areset) !enable |=> $stable(count));

  // Count changes only when enable was 1 (excluding reset cycles)
  assert property (cb disable iff (areset) $changed(count) |-> $past(enable));

  // Coverage
  // See a reset pulse
  cover property (cb areset ##1 !areset);
  // See first increment from reset to 1
  cover property (cb areset ##1 !areset ##1 enable ##1 (count == 4'd1));
  // See a hold while enable is low
  cover property (cb disable iff (areset) !enable [*3]);
  // See wrap-around 15 -> 0 under enable
  cover property (cb disable iff (areset) ($past(count)==4'hF && $past(enable)) |=> (count==4'h0));

endmodule

// Bind to the DUT
bind counter counter_sva u_counter_sva (.clk(clk), .areset(areset), .enable(enable), .count(count));