// SVA for my_and4: checks full functional correctness, X integrity, and basic coverage.
// Bind this module to the DUT.

module my_and4_sva (
  input logic A, B, C, D,
  input logic VPB, VPWR, VGND, VNB,
  input logic X
);
  // Combinational sampling event (fires on any input/output change)
  event comb_e;
  always @* -> comb_e;

  // Functional equivalence: VPB=0 => AND, VPB=1 => OR
  property p_func;
    (!$isunknown({A,B,C,D,VPB})) |->
      (X === (VPB ? (A|B|C|D) : (A&B&C&D)));
  endproperty
  assert property (@(comb_e) p_func)
    else $error("my_and4 func mismatch: VPB=%0b A=%0b B=%0b C=%0b D=%0b X=%0b",
                VPB,A,B,C,D,X);

  // X is never X/Z when inputs and VPB are all known
  assert property (@(comb_e) (!$isunknown({A,B,C,D,VPB})) |-> !$isunknown(X))
    else $error("my_and4 X unknown with known inputs");

  // Mode-specific corner checks (concise, catch common mistakes)
  // AND mode corners
  assert property (@(comb_e) (VPB==1'b0 &&  &{A,B,C,D}) |-> (X==1'b1));
  assert property (@(comb_e) (VPB==1'b0 && ~&{A,B,C,D}) |-> (X==1'b0));
  // OR mode corners
  assert property (@(comb_e) (VPB==1'b1 &&  |{A,B,C,D}) |-> (X==1'b1));
  assert property (@(comb_e) (VPB==1'b1 && ~|{A,B,C,D}) |-> (X==1'b0));

  // Minimal coverage: exercise both modes and extreme cases; observe X toggles
  cover property (@(comb_e) (VPB==1'b0 &&  &{A,B,C,D} && X==1'b1));
  cover property (@(comb_e) (VPB==1'b0 && ~&{A,B,C,D} && X==1'b0));
  cover property (@(comb_e) (VPB==1'b1 &&  |{A,B,C,D} && X==1'b1));
  cover property (@(comb_e) (VPB==1'b1 && ~|{A,B,C,D} && X==1'b0));
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);
endmodule

// Bind to DUT
bind my_and4 my_and4_sva sva_my_and4 (
  .A(A), .B(B), .C(C), .D(D),
  .VPB(VPB), .VPWR(VPWR), .VGND(VGND), .VNB(VNB),
  .X(X)
);