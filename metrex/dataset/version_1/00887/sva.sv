// SVA checker for sky130_fd_sc_hdll__a22o
module sky130_fd_sc_hdll__a22o_sva (
  input logic A1, A2, B1, B2, X,
  input logic and0_out, and1_out, or0_out_X
);
  // Sample on any input transition
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2
  ); endclocking

  // Functional equivalence (four-state)
  assert property (X === ((A1 & A2) | (B1 & B2)));

  // Gate-level internal consistency
  assert property (and0_out  === (B1 & B2));
  assert property (and1_out  === (A1 & A2));
  assert property (or0_out_X === (and1_out | and0_out));
  assert property (X         === or0_out_X);

  // X-propagation sanity: clean inputs => clean outputs
  assert property (!$isunknown({A1,A2,B1,B2}) |-> !$isunknown(X));
  assert property (!$isunknown({A1,A2,B1,B2}) |-> !$isunknown({and0_out,and1_out,or0_out_X}));

  // Targeted functional coverage
  cover property ((A1 & A2) && !(B1 & B2) && X);    // A-term alone drives X=1
  cover property ((B1 & B2) && !(A1 & A2) && X);    // B-term alone drives X=1
  cover property ((A1 & A2) && (B1 & B2) && X);     // Both terms high
  cover property (!((A1 & A2) | (B1 & B2)) && !X);  // Output low
  cover property ($rose(X));
  cover property ($fell(X));
endmodule

// Bind into the DUT (accesses internal nets)
bind sky130_fd_sc_hdll__a22o sky130_fd_sc_hdll__a22o_sva sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .X(X),
  .and0_out(and0_out), .and1_out(and1_out), .or0_out_X(or0_out_X)
);