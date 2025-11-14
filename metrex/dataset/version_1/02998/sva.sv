// SVA for Counter. Bind this to the DUT.
module Counter_sva #(parameter WIDTH=32)
(
  input  logic                 clock,
  input  logic                 reset,
  input  logic [WIDTH-1:0]     max_val,
  input  logic [WIDTH-1:0]     count
);

  default clocking cb @(posedge clock); endclocking

  // Reset behavior: count is 0 whenever reset is 1, and at the first cycle reset goes low.
  assert property (reset |-> count == '0);
  assert property ($fell(reset) |-> count == '0);

  // Core next-state relation (from previous cycle's count and max_val).
  assert property (disable iff (reset)
                   count == (($past(count) == $past(max_val)) ? '0 : $past(count) + 1));

  // No X on count when not in reset.
  assert property (!reset |-> !$isunknown(count));

  // Coverage
  // Increment step
  cover property (disable iff (reset)
                  ($past(count) != $past(max_val)) && (count == $past(count) + 1));

  // Wrap on equality to max_val
  cover property (disable iff (reset)
                  ($past(count) == $past(max_val)) && (count == '0));

  // Special case: max_val == 0 keeps counter at 0
  cover property (disable iff (reset) ($past(max_val) == '0) ##1 (count == '0));

  // Arithmetic overflow corner: count=all 1's, not equal to max_val, next count 0
  cover property (disable iff (reset)
                  ($past(count) == {WIDTH{1'b1}}) && ($past(max_val) != $past(count)) && (count == '0));

  // Exercise dynamic max_val change
  cover property (disable iff (reset) $changed(max_val));

endmodule

bind Counter Counter_sva #(.WIDTH(32)) u_counter_sva (
  .clock(clock),
  .reset(reset),
  .max_val(max_val),
  .count(count)
);