// SVA for mux2to1 — bindable checker (concise, high-quality)
`ifndef SYNTHESIS
module mux2to1_sva (input logic A, B, SEL, OUT);
  `define AE(s) posedge s or negedge s

  // Functional equivalence on any input change (sample after update)
  assert property (@(`AE(A) or `AE(B) or `AE(SEL)))
                   1 |-> ##0 (OUT === (SEL ? B : A));

  // Selected data must pass through on its change
  assert property (@(`AE(A)) !SEL |-> ##0 (OUT === A));
  assert property (@(`AE(B))  SEL |-> ##0 (OUT === B));

  // No X/Z allowed on interface
  assert property (@(`AE(A) or `AE(B) or `AE(SEL) or `AE(OUT)))
                   !$isunknown({A,B,SEL,OUT});

  // Coverage: both selections and data tracking when selected
  cover property (@(negedge SEL) ##0 (OUT === A));
  cover property (@(posedge SEL) ##0 (OUT === B));
  cover property (@(`AE(A)) !SEL ##0 (OUT === A));
  cover property (@(`AE(B))  SEL ##0 (OUT === B));
endmodule

bind mux2to1 mux2to1_sva u_mux2to1_sva(.A(A), .B(B), .SEL(SEL), .OUT(OUT));
`endif