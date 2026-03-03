// SVA checker for logic_circuit
module logic_circuit_sva (
  input logic A1, A2, B1, C1, D1,
  input logic X,
  input logic VPWR, VGND, VPB, VNB
);

  // Helper terms
  logic t1 = A1 & A2;
  logic t2 = ~A1 & B1;
  logic t3 = ~C1 & D1;

  // Shorthand event: re-sample on any relevant toggle
  `define COMB_EV (posedge A1 or negedge A1 or \
                    posedge A2 or negedge A2 or \
                    posedge B1 or negedge B1 or \
                    posedge C1 or negedge C1 or \
                    posedge D1 or negedge D1 or \
                    posedge X  or negedge X)

  // Functional equivalence (4-state safe)
  assert property (@`COMB_EV) (X === (t1 | t2 | t3));

  // When inputs are 2-state, output must be 2-state and correct
  assert property (@`COMB_EV)
    (!$isunknown({A1,A2,B1,C1,D1})) |-> (! $isunknown(X) && (X == (t1 | t2 | t3)));

  // No spurious output changes
  assert property (@`COMB_EV) $changed(X) |-> $changed({A1,A2,B1,C1,D1});

  // Power pins constant
  assert property (@`COMB_EV) (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Coverage: exercise each signal edge
  cover property (@`COMB_EV) $rose(A1);  cover property (@`COMB_EV) $fell(A1);
  cover property (@`COMB_EV) $rose(A2);  cover property (@`COMB_EV) $fell(A2);
  cover property (@`COMB_EV) $rose(B1);  cover property (@`COMB_EV) $fell(B1);
  cover property (@`COMB_EV) $rose(C1);  cover property (@`COMB_EV) $fell(C1);
  cover property (@`COMB_EV) $rose(D1);  cover property (@`COMB_EV) $fell(D1);
  cover property (@`COMB_EV) $rose(X);   cover property (@`COMB_EV) $fell(X);

  // Coverage: each implicant alone drives X high
  cover property (@`COMB_EV) disable iff ($isunknown({A1,A2,B1,C1,D1}))
    ( t1 && !t2 && !t3 ) ##0 X;
  cover property (@`COMB_EV) disable iff ($isunknown({A1,A2,B1,C1,D1}))
    (!t1 &&  t2 && !t3 ) ##0 X;
  cover property (@`COMB_EV) disable iff ($isunknown({A1,A2,B1,C1,D1}))
    (!t1 && !t2 &&  t3 ) ##0 X;

  // Coverage: overlaps and all-off
  cover property (@`COMB_EV) disable iff ($isunknown({A1,A2,B1,C1,D1}))
    ( t1 &&  t2 && !t3) ##0 X;
  cover property (@`COMB_EV) disable iff ($isunknown({A1,A2,B1,C1,D1}))
    ( t1 && !t2 &&  t3) ##0 X;
  cover property (@`COMB_EV) disable iff ($isunknown({A1,A2,B1,C1,D1}))
    (!t1 &&  t2 &&  t3) ##0 X;
  cover property (@`COMB_EV) disable iff ($isunknown({A1,A2,B1,C1,D1}))
    ( t1 &&  t2 &&  t3) ##0 X;
  cover property (@`COMB_EV) disable iff ($isunknown({A1,A2,B1,C1,D1}))
    (!t1 && !t2 && !t3) ##0 !X;

  `undef COMB_EV
endmodule

// Bind into DUT
bind logic_circuit logic_circuit_sva sva_i (
  .A1(A1), .A2(A2), .B1(B1), .C1(C1), .D1(D1), .X(X),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);