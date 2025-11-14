// SVA checker bound to my_nor4. Focused, concise, and comprehensive for a pure-comb cell.
module my_nor4_sva;

  // Fire on any input edge
  `define EV (posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D_N or negedge D_N)

  // Functional equivalence (gate-level structure simplifies to (A|B)&(C|D_N))
  assert property (@(`EV) (!$isunknown({A,B,C,D_N})) |-> (Y == ((A|B) & (C|D_N))));

  // Internal net consistency
  assert property (@(`EV) (!$isunknown({A,B}))     |-> (AB   == ~(A|B)));
  assert property (@(`EV) (!$isunknown({C,D_N}))   |-> (CD   == ~(C|D_N)));
  assert property (@(`EV) (!$isunknown({AB,CD}))   |-> (ABCD == ~(AB|CD)));
  assert property (@(`EV) (!$isunknown({AB,CD}))   |-> (Y    == ~(AB|CD)));

  // No X/Z propagation when inputs are known
  assert property (@(`EV) (!$isunknown({A,B,C,D_N})) |-> (!$isunknown({AB,CD,ABCD,Y})));

  // Coverage: output activity
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) &&  Y);
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) && !Y);
  cover property (@(`EV) $rose(Y));
  cover property (@(`EV) $fell(Y));

  // Coverage: OR-group cross states (covers all four combinations)
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) && !(A|B) &&  (C|D_N));
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) &&  (A|B) && !(C|D_N));
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) && !(A|B) && !(C|D_N));
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) &&  (A|B) &&  (C|D_N)); // same as Y==1

  // Coverage: each input individually drives its OR group
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) &&  A && !B && (C|D_N));
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) &&  B && !A && (C|D_N));
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) &&  C && !D_N && (A|B));
  cover property (@(`EV) (!$isunknown({A,B,C,D_N})) &&  D_N && !C && (A|B));

endmodule

bind my_nor4 my_nor4_sva sva_i();