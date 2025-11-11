// SVA for sky130_fd_sc_ls__o2111a
// Bind-in checks and coverage; clockless, event-driven sampling.

module sky130_fd_sc_ls__o2111a_sva
(
  input logic A1, A2, B1, C1, D1,
  input logic X,
  input logic and1_out, and2_out, and3_out, and4_out,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any relevant signal change
  default clocking cb @(A1 or A2 or B1 or C1 or D1 or
                        X or and1_out or and2_out or and3_out or and4_out or
                        VPWR or VGND or VPB or VNB); endclocking

  // Functional equivalence (4-state aware)
  assert property (X === (A1 & A2 & B1 & C1 & D1));

  // Structural node equivalence
  assert property (and1_out === (A1 & A2));
  assert property (and2_out === (B1 & C1));
  assert property (and3_out === (C1 & D1));
  assert property (and4_out === (and1_out & and2_out & and3_out));
  assert property (X === and4_out);

  // Zero domination
  assert property ((A1===1'b0) |-> (X===1'b0));
  assert property ((A2===1'b0) |-> (X===1'b0));
  assert property ((B1===1'b0) |-> (X===1'b0));
  assert property ((C1===1'b0) |-> (X===1'b0));
  assert property ((D1===1'b0) |-> (X===1'b0));

  // All-ones drives 1
  assert property ((A1===1 && A2===1 && B1===1 && C1===1 && D1===1) |-> (X===1));

  // No X/Z on output when inputs are known
  assert property ((!$isunknown({A1,A2,B1,C1,D1})) |-> (!$isunknown(X)));

  // Power rails sanity
  assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Basic coverage
  cover property (X===1'b1);
  cover property (X===1'b0);
  cover property ($rose(X));
  cover property ($fell(X));

  cover property ($rose(A1)); cover property ($fell(A1));
  cover property ($rose(A2)); cover property ($fell(A2));
  cover property ($rose(B1)); cover property ($fell(B1));
  cover property ($rose(C1)); cover property ($fell(C1));
  cover property ($rose(D1)); cover property ($fell(D1));

  // Cover minterm that makes X high
  cover property (A1===1 && A2===1 && B1===1 && C1===1 && D1===1 && X===1);

  // Optional: cover X-propagation through C1 when others 1
  cover property (A1===1 && A2===1 && B1===1 && D1===1 && C1===1'bx && $isunknown(X));

endmodule

bind sky130_fd_sc_ls__o2111a sky130_fd_sc_ls__o2111a_sva sva_i (.*);