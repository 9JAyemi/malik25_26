// SVA for mux4to1. Bind this to the DUT.
// Focused, X-safe functional checks + essential coverage.

module mux4to1_sva (
  input logic A, B, C, D,
  input logic sel0, sel1,
  input logic Y,
  input logic w1, w2, w3, w4, w5, w6
);
  // Local decodes
  logic g1, g2, g3, g4;
  assign g1 = (~sel1 & ~sel0);
  assign g2 = (~sel1 &  sel0);
  assign g3 = ( sel1 & ~sel0);
  assign g4 = ( sel1 &  sel0);

  // Decode must be one-hot when selects are known
  assert property (@(A or B or C or D or sel0 or sel1)
    (!$isunknown({sel1,sel0})) |-> $onehot({g1,g2,g3,g4})
  );

  // Functional correctness and X-safety when all drivers are known
  assert property (@(A or B or C or D or sel0 or sel1)
    (!$isunknown({A,B,C,D,sel0,sel1})) |->
      (Y === ((g1 & A) | (g2 & B) | (g3 & C) | (g4 & D)))
  );

  // Structure cross-checks (catch unintended edits)
  assert property (@(A or B or C or D or sel0 or sel1)
    ((w1 === (g1 & A)) && (w2 === (g2 & B)) && (w3 === (g3 & C)) && (w4 === (g4 & D)))
  );
  assert property (@(A or B or C or D or sel0 or sel1)
    ((w5 === (w1 | w2)) && (w6 === (w3 | w4)) && (Y === (w5 | w6)))
  );

  // Partition sanity: upper/lower halves mutually exclusive when sel1 known
  assert property (@(A or B or C or D or sel0 or sel1)
    (!sel1 && !$isunknown(sel1)) |-> (w6 === 1'b0)
  );
  assert property (@(A or B or C or D or sel0 or sel1)
    ( sel1 && !$isunknown(sel1)) |-> (w5 === 1'b0)
  );

  // Coverage: see all select codes
  cover property (@(sel0 or sel1) (!$isunknown({sel0,sel1}) && g1));
  cover property (@(sel0 or sel1) (!$isunknown({sel0,sel1}) && g2));
  cover property (@(sel0 or sel1) (!$isunknown({sel0,sel1}) && g3));
  cover property (@(sel0 or sel1) (!$isunknown({sel0,sel1}) && g4));

  // Coverage: selected input change propagates to Y in same timestep
  cover property (@(A) (g1 && !$isunknown({A,sel0,sel1}) && $changed(A)) |-> ##0 ($changed(Y) && (Y === A)));
  cover property (@(B) (g2 && !$isunknown({B,sel0,sel1}) && $changed(B)) |-> ##0 ($changed(Y) && (Y === B)));
  cover property (@(C) (g3 && !$isunknown({C,sel0,sel1}) && $changed(C)) |-> ##0 ($changed(Y) && (Y === C)));
  cover property (@(D) (g4 && !$isunknown({D,sel0,sel1}) && $changed(D)) |-> ##0 ($changed(Y) && (Y === D)));
endmodule

bind mux4to1 mux4to1_sva i_mux4to1_sva (
  .A(A), .B(B), .C(C), .D(D),
  .sel0(sel0), .sel1(sel1),
  .Y(Y),
  .w1(w1), .w2(w2), .w3(w3), .w4(w4), .w5(w5), .w6(w6)
);