// SVA for bitwise_or. Bind this to the DUT.
// Focus: correctness when enabled, hold when disabled, no unintended updates,
// and concise functional coverage of OR behavior.

module bitwise_or_assert
(
  input logic        clk,
  input logic        enable,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [7:0]  result
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness on enable
  assert property (enable && !$isunknown({A,B}) |-> result == (A | B));

  // Hold behavior when disabled
  assert property (!enable |-> result == $past(result));

  // Result only changes on cycles with enable asserted
  assert property ($changed(result) |-> enable);

  // Basic sanity: if last result was known and we’re disabled, keep it known
  assert property (!enable && !$isunknown($past(result)) |-> !$isunknown(result));

  // ----------------
  // Functional coverage
  // ----------------

  // Hit all four bitwise OR input/output cases somewhere in the word on enabled cycles
  cover property (enable && result==(A|B) && |(~(A|B)));       // exists bit: 0|0 -> 0
  cover property (enable && result==(A|B) && |(A & ~B));        // exists bit: 1|0 -> 1
  cover property (enable && result==(A|B) && |(~A & B));        // exists bit: 0|1 -> 1
  cover property (enable && result==(A|B) && |(A & B));         // exists bit: 1|1 -> 1

  // Extremes: all-zero and all-one OR results
  cover property (enable && (A|B)==8'h00 && result==8'h00);
  cover property (enable && (A|B)==8'hFF && result==8'hFF);

  // Observe an actual update and a disabled hold streak
  cover property (enable && $changed(result));
  cover property (!enable ##1 !enable && $stable(result));

endmodule

bind bitwise_or bitwise_or_assert sva (.*);