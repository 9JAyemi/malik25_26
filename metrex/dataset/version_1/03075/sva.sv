// SVA for my_module
module my_module_sva (
  input X,
  input A1, A2, A3,
  input B1, C1,
  input VPWR, VGND,
  input VPB, VNB
);

  // Functional equivalence (single golden check)
  assert property (@(*)
    X === ((A1 & A2 & A3) | (B1 | C1) | (VPB ^ VNB) | (VPWR & VGND))
  );

  // Output should only change when some input changes
  assert property (@(posedge X or negedge X)
    $changed({A1,A2,A3,B1,C1,VPWR,VGND,VPB,VNB})
  );

  // If all inputs are stable, output must be stable
  assert property (@(*)
    $stable({A1,A2,A3,B1,C1,VPWR,VGND,VPB,VNB}) |-> $stable(X)
  );

  // No X/Z on output when all inputs are known
  assert property (@(*)
    !$isunknown({A1,A2,A3,B1,C1,VPWR,VGND,VPB,VNB}) |-> !$isunknown(X)
  );

  // Term-specific single-cause coverage (prove each term can exclusively drive X)
  cover property (@(*)
    (A1 & A2 & A3) && !(B1|C1) && (VPB==VNB) && !(VPWR & VGND) && (X==1)
  ); // AND-only

  cover property (@(*)
    !(A1 & A2 & A3) && (B1|C1) && (VPB==VNB) && !(VPWR & VGND) && (X==1)
  ); // OR-only

  cover property (@(*)
    !(A1 & A2 & A3) && !(B1|C1) && (VPB^VNB) && !(VPWR & VGND) && (X==1)
  ); // XOR-only

  cover property (@(*)
    !(A1 & A2 & A3) && !(B1|C1) && (VPB==VNB) && (VPWR & VGND) && (X==1)
  ); // POWER-only

  // Output low coverage (all terms false)
  cover property (@(*)
    !(A1 & A2 & A3) && !(B1|C1) && (VPB==VNB) && !(VPWR & VGND) && (X==0)
  );

  // Basic toggle coverage
  cover property (@(*) $rose(X));
  cover property (@(*) $fell(X));

  cover property (@(*) $rose(A1));  cover property (@(*) $fell(A1));
  cover property (@(*) $rose(A2));  cover property (@(*) $fell(A2));
  cover property (@(*) $rose(A3));  cover property (@(*) $fell(A3));
  cover property (@(*) $rose(B1));  cover property (@(*) $fell(B1));
  cover property (@(*) $rose(C1));  cover property (@(*) $fell(C1));
  cover property (@(*) $rose(VPWR)); cover property (@(*) $fell(VPWR));
  cover property (@(*) $rose(VGND)); cover property (@(*) $fell(VGND));
  cover property (@(*) $rose(VPB));  cover property (@(*) $fell(VPB));
  cover property (@(*) $rose(VNB));  cover property (@(*) $fell(VNB));

endmodule

// Bind into DUT
bind my_module my_module_sva sva_inst (.*);