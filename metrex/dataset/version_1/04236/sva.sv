// SVA for comparator_16bit
module comparator_16bit_sva (input [15:0] a, b, input eq);

  // Functional correctness including 4-state (X/Z) behavior
  assert property (@(a or b or eq) eq === (a == b));

  // Sanity on X-propagation
  assert property (@(a or b) !$isunknown({a,b}) |-> !$isunknown(eq));
  assert property (@(a or b)  $isunknown({a,b}) |->  $isunknown(eq));

  // Coverage: equal, not-equal, unknowns, single-bit difference, and eq edges
  cover  property (@(a or b) !$isunknown({a,b}) && (a == b) && (eq == 1));
  cover  property (@(a or b) !$isunknown({a,b}) && (a != b) && (eq == 0));
  cover  property (@(a or b)  $isunknown({a,b}) &&  $isunknown(eq));
  cover  property (@(a or b) !$isunknown({a,b}) && $onehot(a ^ b));
  cover  property (@(posedge eq) 1);
  cover  property (@(negedge eq) 1);

endmodule

bind comparator_16bit comparator_16bit_sva i_comparator_16bit_sva (.a(a), .b(b), .eq(eq));