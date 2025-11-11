// SVA for four_input_OR
module four_input_OR_sva;

  // Bind inside DUT scope to see internal nets
  default clocking cb @(*); endclocking
  default disable iff (!(VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0));

  // Rails sanity
  assert property (VPWR===1 && VPB===1 && VGND===0 && VNB===0);

  // Functional correctness (known inputs => known, correct output)
  assert property (!$isunknown({A,B,C,D}) |-> (X == (A|B|C|D)) && !$isunknown(X));

  // Strong 4-state implications
  assert property ((A===1 || B===1 || C===1 || D===1) |-> X===1);
  assert property ((A===0 && B===0 && C===0 && D===0) |-> X===0);

  // Structural checks of internal decomposition
  assert property (AB   === (A|B));
  assert property (CD   === (C|D));
  assert property (ABCD === (AB|CD));
  assert property (X    === ABCD);

  // Coverage: all 16 input combinations with expected X
  genvar i;
  generate
    for (i=0; i<16; i++) begin: g_in_cov
      cover property ( {A,B,C,D} === i[3:0] && X === (|i) );
    end
  endgenerate

  // Coverage: each input alone controls X (others 0) in both directions
  cover property (rose(A) && !B && !C && !D && $stable({B,C,D}) && rose(X));
  cover property (fell(A) && !B && !C && !D && $stable({B,C,D}) && fell(X));
  cover property (rose(B) && !A && !C && !D && $stable({A,C,D}) && rose(X));
  cover property (fell(B) && !A && !C && !D && $stable({A,C,D}) && fell(X));
  cover property (rose(C) && !A && !B && !D && $stable({A,B,D}) && rose(X));
  cover property (fell(C) && !A && !B && !D && $stable({A,B,D}) && fell(X));
  cover property (rose(D) && !A && !B && !C && $stable({A,B,C}) && rose(X));
  cover property (fell(D) && !A && !B && !C && $stable({A,B,C}) && fell(X));

  // Output toggling coverage
  cover property (rose(X));
  cover property (fell(X));

endmodule

bind four_input_OR four_input_OR_sva sva();