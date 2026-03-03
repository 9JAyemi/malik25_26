// SVA for and4. Bind this to the DUT.
// Focus: correctness, internal consistency, X-propagation, hazard check, and concise coverage.
bind and4 and4_sva and4_sva_inst();

module and4_sva;

  // Functional correctness (4-state exact)
  assert property (@(A or B or C or D) X === (A & B & C & D));

  // Internal gate correctness (4-state exact)
  assert property (@(A or B)       and0_out === (A & B));
  assert property (@(C or D)       and1_out === (C & D));
  assert property (@(and0_out or and1_out) X === (and0_out & and1_out));

  // No X on output when all inputs known
  assert property (@(A or B or C or D or X) !$isunknown({A,B,C,D}) |-> !$isunknown(X));

  // No spurious output toggle without any input change
  assert property (@(A or B or C or D or X) $changed(X) |-> !$stable({A,B,C,D}));

  // Coverage: key categories of input combinations and output transitions
  cover property (@(A or B or C or D) !$isunknown({A,B,C,D}) && {A,B,C,D} == 4'b0000);
  cover property (@(A or B or C or D) !$isunknown({A,B,C,D}) && $countones({A,B,C,D}) == 1);
  cover property (@(A or B or C or D) !$isunknown({A,B,C,D}) && $countones({A,B,C,D}) == 2);
  cover property (@(A or B or C or D) !$isunknown({A,B,C,D}) && $countones({A,B,C,D}) == 3);
  cover property (@(A or B or C or D) !$isunknown({A,B,C,D}) && {A,B,C,D} == 4'b1111);

  // Coverage: output toggles and intermediate gate highs
  cover property (@(A or B or C or D or X) $rose(X));
  cover property (@(A or B or C or D or X) $fell(X));
  cover property (@(A or B) and0_out);
  cover property (@(C or D) and1_out);

endmodule