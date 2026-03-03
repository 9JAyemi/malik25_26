// SVA checker for counter
module counter_sva (
  input  logic       clk,
  input  logic       reset,   // active-low async reset
  input  logic [3:0] count
);

  // Track if reset went low since last clk edge
  logic reset_low_seen;
  always @(negedge reset or posedge clk) begin
    if (!reset)               reset_low_seen <= 1'b1;
    else if (reset)           reset_low_seen <= 1'b0; // clear on clk when reset is high
  end

  // Basic sanity: no X on reset at clk sampling
  assert property (@(posedge clk) !$isunknown(reset))
    else $error("reset is X/Z at posedge clk");

  // Async reset must clear immediately (after NBA of the same timestep)
  assert property (@(negedge reset) ##0 (count == 4'h0))
    else $error("count not cleared immediately on async reset");

  // While reset is low, count is 0 and known
  assert property (@(posedge clk) !reset |-> (count == 4'h0 && !$isunknown(count)))
    else $error("count not 0/known while reset low");

  // No X on count once reset is high
  assert property (@(posedge clk) reset |-> !$isunknown(count))
    else $error("count X/Z while reset high");

  // Normal +1 increment when no async reset occurred between consecutive clks
  assert property (@(posedge clk)
                   reset && !reset_low_seen && $past(reset) && !$past(reset_low_seen)
                   |-> count == ($past(count) + 4'd1))
    else $error("count failed +1 increment without intervening reset");

  // First tick after any async reset that occurred between clks yields 1
  assert property (@(posedge clk)
                   reset && reset_low_seen
                   |-> count == 4'd1)
    else $error("count not 1 on first clk after async reset between clks");

  // Explicit wrap-around check (no intervening reset)
  assert property (@(posedge clk)
                   reset && !reset_low_seen && $past(reset) && !$past(reset_low_seen) && ($past(count)==4'hF)
                   |-> count == 4'h0)
    else $error("count failed 0xF->0x0 wrap without intervening reset");

  // Coverage
  cover property (@(negedge reset) 1'b1); // saw async reset
  cover property (@(posedge clk) reset && !reset_low_seen && $past(reset) && !$past(reset_low_seen)
                  && (count == ($past(count)+4'd1))); // normal increment
  cover property (@(posedge clk) reset && !reset_low_seen && $past(reset) && !$past(reset_low_seen)
                  && ($past(count)==4'hF) && (count==4'h0)); // wrap-around
  cover property (@(posedge clk) reset && reset_low_seen && (count==4'd1)); // post-async-reset first increment

endmodule

// Bind to DUT
bind counter counter_sva u_counter_sva (.clk(clk), .reset(reset), .count(count));