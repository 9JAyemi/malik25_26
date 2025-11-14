// SVA for constant_enable
module constant_enable_sva (
  input clk,
  input reset,
  input enable,
  input out
);

  // Default clock for synchronous checks
  default clocking cb @(posedge clk); endclocking

  // Async reset must clear out immediately
  assert property (@(posedge reset) ##0 (out == 1'b0))
    else $error("out not cleared immediately on async reset");

  // While reset is asserted, out must be 0 on every clk
  assert property (reset |-> (out == 1'b0))
    else $error("out not 0 while reset is asserted at clk edge");

  // Functional mapping: out mirrors enable when not in reset
  assert property (disable iff (reset) (out == enable))
    else $error("out != enable when reset=0 at clk edge");

  // If out is 1, then enable must be 1 and reset must be 0
  assert property (out |-> (!reset && enable))
    else $error("out=1 without enable=1 or with reset=1");

  // No X/Z on key signals at clk edge
  assert property (!$isunknown({reset, enable, out}))
    else $error("X/Z detected on reset/enable/out at clk edge");

  // No X/Z on out immediately after async reset
  assert property (@(posedge reset) ##0 !$isunknown(out))
    else $error("X/Z on out after async reset");

  // out can only change on clk or async reset edges (no glitches)
  assert property (@(posedge out or negedge out) ($rose(clk) || $rose(reset)))
    else $error("out changed without clk or reset edge");

  // Coverage
  cover property (@(posedge reset) 1);                         // saw async reset
  cover property (disable iff (reset) $rose(out));             // out 0->1
  cover property (disable iff (reset) $fell(out));             // out 1->0
  cover property (@(posedge reset) enable);                    // reset while enable=1

endmodule

bind constant_enable constant_enable_sva sva (.clk(clk), .reset(reset), .enable(enable), .out(out));