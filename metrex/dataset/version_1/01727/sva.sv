// SVA for up_counter
module up_counter_sva (input logic clk, reset, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Track if reset has ever been seen (for X-check gating)
  bit seen_reset;
  always_ff @(posedge clk) if (reset) seen_reset <= 1'b1;

  // Synchronous reset: drives and holds 0 while asserted
  assert property (reset |-> count == 4'h0);
  assert property (disable iff ($initstate)
                   (reset && $past(reset)) |-> count == 4'h0);

  // Normal increment when not wrapping
  assert property (disable iff ($initstate)
                   (!reset && !$past(reset) && $past(count) != 4'hF)
                   |-> (count == $past(count) + 4'd1));

  // Wrap from 15->0
  assert property (disable iff ($initstate)
                   (!reset && !$past(reset) && $past(count) == 4'hF)
                   |-> (count == 4'h0));

  // Must change every non-reset cycle
  assert property (disable iff ($initstate)
                   (!reset && !$past(reset)) |-> (count != $past(count)));

  // No X/Z on count after a reset has been observed
  assert property (seen_reset |-> !$isunknown(count));

  // — Coverage —
  // See a reset pulse
  cover property ($rose(reset));

  // See a normal increment
  cover property (disable iff ($initstate)
                  (!reset && !$past(reset) && $past(count) != 4'hF &&
                   count == $past(count) + 4'd1));

  // See the wrap-around
  cover property (disable iff ($initstate)
                  (!reset && !$past(reset) && $past(count) == 4'hF && count == 4'h0));

  // Observe a full 0..15..0 cycle (no resets during the run)
  cover property (disable iff (reset || $initstate)
                  (count==4'h0)
              ##1 (count==4'h1)
              ##1 (count==4'h2)
              ##1 (count==4'h3)
              ##1 (count==4'h4)
              ##1 (count==4'h5)
              ##1 (count==4'h6)
              ##1 (count==4'h7)
              ##1 (count==4'h8)
              ##1 (count==4'h9)
              ##1 (count==4'hA)
              ##1 (count==4'hB)
              ##1 (count==4'hC)
              ##1 (count==4'hD)
              ##1 (count==4'hE)
              ##1 (count==4'hF)
              ##1 (count==4'h0));

endmodule

// Bind into DUT
bind up_counter up_counter_sva sva_inst(.clk(clk), .reset(reset), .count(count));