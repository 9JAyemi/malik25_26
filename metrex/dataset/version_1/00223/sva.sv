// SVA checker for mux2
module mux2_sva (
  input logic X, A0, A1, S,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any input edge
  default clocking cb @(posedge A0 or negedge A0 or
                         posedge A1 or negedge A1 or
                         posedge S  or negedge S); endclocking

  // Functional correctness (including X/Z semantics on S)
  assert property (S===1 |-> X===A1);
  assert property (S===0 |-> X===A0);
  assert property (((S!==1) && (S!==0) && (A0===A1)) |-> (X===A0));
  assert property (((S!==1) && (S!==0) && (A0!==A1)) |-> $isunknown(X));

  // Selection edge behavior
  assert property ($rose(S) |-> X===A1);
  assert property ($fell(S) |-> X===A0);

  // Pass-through and isolation on data changes
  assert property ((S===0 && $changed(A0)) |-> (X===A0 && $changed(X)));
  assert property ((S===1 && $changed(A1)) |-> (X===A1 && $changed(X)));
  assert property ((S===0 && $changed(A1)) |-> ($stable(X) && X===A0));
  assert property ((S===1 && $changed(A0)) |-> ($stable(X) && X===A1));

  // Supply rails (should remain tied)
  assert property (VPWR===1 && VPB===1 && VGND===0 && VNB===0);

  // Coverage
  cover property (S===0 && X===A0);
  cover property (S===1 && X===A1);
  cover property ((S!==0 && S!==1) && (A0!==A1) && $isunknown(X));
  cover property ((S!==0 && S!==1) && (A0===A1) && (X===A0));
  cover property (S===0 && $changed(A0) && $changed(X) && X===A0);
  cover property (S===1 && $changed(A1) && $changed(X) && X===A1);
  cover property (S===0 && $changed(A1) && $stable(X));
  cover property (S===1 && $changed(A0) && $stable(X));
  cover property ($rose(S));
  cover property ($fell(S));
  cover property ($rose(X));
  cover property ($fell(X));

endmodule

bind mux2 mux2_sva u_mux2_sva(.X(X), .A0(A0), .A1(A1), .S(S), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB));