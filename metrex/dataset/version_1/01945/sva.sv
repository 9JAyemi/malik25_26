// SVA checker for min_shift_register
// Bind this module to the DUT to verify functionality and provide coverage.

module min_shift_register_sva
(
  input logic         clk,
  input logic  [7:0]  a, b, c, d,
  input logic  [7:0]  min,
  input logic         q,
  input logic  [7:0]  final_output
);
  default clocking cb @(posedge clk); endclocking

  // Helper fns that mirror DUT’s strict-tie behavior (< prefers right operand on ties)
  function automatic logic [7:0] min2_strict(input logic [7:0] x, y);
    min2_strict = (x < y) ? x : y;
  endfunction
  function automatic logic [7:0] min4_strict(input logic [7:0] ai, bi, ci, di);
    logic [7:0] ab, cd;
    ab = min2_strict(ai, bi);
    cd = min2_strict(ci, di);
    return min2_strict(ab, cd);
  endfunction

  // Start flag to make $past() safe without a reset
  logic started;
  initial started = 0;
  always @(posedge clk) started <= 1'b1;

  // Core functional correctness: combinational minimum computation
  assert property (min == min4_strict(a, b, c, d))
    else $error("min mismatch: min=%0d exp=%0d", min, min4_strict(a,b,c,d));

  // Registered behavior: final_output holds previous-cycle min
  assert property (disable iff (!started) final_output == $past(min))
    else $error("final_output is not previous-cycle min");

  // q must be LSB of the registered output
  assert property (q === final_output[0])
    else $error("q != final_output[0]");

  // final_output must not glitch between clock edges
  assert property ($stable(final_output) throughout (!clk))
    else $error("final_output glitches between clock edges");

  // Optional X-propagation sanity checks: outputs must be known if inputs are known
  assert property (!$isunknown({a,b,c,d}) |-> !$isunknown(min))
    else $error("min has X/Z while inputs are known");
  assert property (disable iff (!started) !$isunknown($past(min)) |-> !$isunknown(final_output))
    else $error("final_output has X/Z while prior min was known");
  assert property (!$isunknown(final_output[0]) |-> !$isunknown(q))
    else $error("q has X/Z while final_output[0] known");

  // Coverage: exercise all comparator paths and selections
  // Per-input selection as global minimum (reflects strict-tie behavior)
  cover property (min == a);
  cover property (min == b);
  cover property (min == c);
  cover property (min == d);

  // Pairwise comparator branches (ties and strict-less)
  cover property (a < b);
  cover property (a == b);
  cover property (c < d);
  cover property (c == d);

  // Top-level compare branch coverage using same strict-tie function
  let min_ab = min2_strict(a,b);
  let min_cd = min2_strict(c,d);
  cover property (min_ab <  min_cd);
  cover property (min_ab == min_cd);

  // Dynamic behavior coverage
  cover property (disable iff (!started) $changed(min) |=> $changed(final_output));
  cover property ($changed(q));             // q toggles at least once
  cover property (a==b && b==c && c==d);   // all-equal tie case

endmodule

// Bind the checker to the DUT
bind min_shift_register min_shift_register_sva sva(
  .clk(clk),
  .a(a), .b(b), .c(c), .d(d),
  .min(min),
  .q(q),
  .final_output(final_output)
);