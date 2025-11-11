// SVA for Comparator. Bind this to the DUT.
// Focus: functional correctness, mutual exclusivity, no-X, and essential coverage.

module Comparator_sva #(parameter int n = 8)
(
  input  logic [n-1:0] a,
  input  logic [n-1:0] b,
  input  logic         gt,
  input  logic         lt,
  input  logic         eq
);

  default clocking cb @ (posedge $global_clock); endclocking

  // Sanity: outputs are known (no X/Z)
  ap_no_x:   assert property (!$isunknown({gt, lt, eq}));

  // Functional correctness
  ap_gt:     assert property (gt == (a > b));
  ap_lt:     assert property (lt == (a < b));
  ap_eq:     assert property (eq == (a == b));

  // Exactly one outcome must be true
  ap_onehot: assert property ($onehot({gt, lt, eq}));

  // Core outcome coverage
  cp_gt:     cover property (a > b && gt);
  cp_lt:     cover property (a < b && lt);
  cp_eq:     cover property (a == b && eq);

  // Corner coverage
  cp_minmin: cover property (a == '0 && b == '0 && eq);
  cp_maxmax: cover property (a == {n{1'b1}} && b == {n{1'b1}} && eq);
  cp_minmax: cover property (a == '0 && b == {n{1'b1}} && lt);
  cp_maxmin: cover property (a == {n{1'b1}} && b == '0 && gt);

  // Single-bit-difference cases (the differing bit alone determines outcome)
  cp_1bit_gt: cover property ($onehot(a ^ b) && gt);
  cp_1bit_lt: cover property ($onehot(a ^ b) && lt);

endmodule

bind Comparator Comparator_sva #(.n(n)) comparator_sva_bind (.*);