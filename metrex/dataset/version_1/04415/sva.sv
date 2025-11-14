// SVA checker for MX2X4A12TR
// Function reduces to: Y == (B | S0). A is functionally irrelevant.
// Includes internal net consistency checks and concise functional coverage.

module MX2X4A12TR_sva (
  input logic A, B, S0, Y,
  input logic N1, N2, N3, N4, N5, N6
);
  // Sample on any input edge; use ##0 to evaluate after combinational settle
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge S0 or negedge S0); endclocking

  // Functional equivalence and X-prop sanity
  assert property (##0 (Y === (B | S0)));
  assert property (##0 (!$isunknown({A,B,S0}) |-> !$isunknown(Y)));

  // Behavioral checks
  assert property (@(posedge B or negedge B) ##0 (S0==1'b0) |-> (Y==B));   // S0=0: Y follows B
  assert property (@(posedge S0)           ##0 (Y==1'b1));                  // S0=1: Y forced high
  assert property (@(negedge S0)           ##0 (Y==B));                     // S0 falling: Y returns to B
  assert property (@(posedge A or negedge A) ##0 $stable({B,S0}) |-> $stable(Y)); // A does not affect Y

  // Internal net correctness
  assert property (##0 (N1 === ~B));
  assert property (##0 (N5 === ~N1));                // N5 == B
  assert property (##0 (N2 === (A & B)));
  assert property (##0 (N3 === (S0 & N1)));          // == S0 & ~B
  assert property (##0 (N4 === (S0 & A)));
  assert property (##0 (N6 === (N2 | N4)));          // == A & (B | S0)
  assert property (##0 ((Y) === (N3 | N5 | N6)));

  // Compact functional coverage
  cover property (##0 (S0==0 && B==0 && Y==0));
  cover property (##0 (S0==0 && B==1 && Y==1));
  cover property (##0 (S0==1 && B==0 && Y==1));
  cover property (##0 (S0==1 && B==1 && Y==1));
  cover property (@(posedge A or negedge A) ##0 $stable({B,S0}) && $stable(Y));
  cover property (@(posedge S0) ##0 Y==1);

endmodule

// Bind into the DUT so internals (N1..N6) are visible via .*
bind MX2X4A12TR MX2X4A12TR_sva u_MX2X4A12TR_sva (.*);