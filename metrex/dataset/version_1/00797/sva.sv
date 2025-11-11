// SVA checker for sky130_fd_sc_ms__or3b
// Function: X = A | B | ~C_N

module sky130_fd_sc_ms__or3b_sva (
  input logic A,
  input logic B,
  input logic C_N,
  input logic X,
  // internal wires (bound to DUT internals)
  input logic not0_out,
  input logic or0_out_X
);

  // Functional equivalence at the port-level (4-state exact)
  assert property (@(*)) X === (A | B | ~C_N);

  // No X/Z on output when inputs are known
  assert property (@(*)) !($isunknown({A,B,C_N})) |-> !($isunknown(X));

  // Internal structure checks (4-state exact)
  assert property (@(*)) not0_out  === ~C_N;
  assert property (@(*)) or0_out_X === (A | B | not0_out);
  assert property (@(*)) X         === or0_out_X;

  // Input-space coverage (all 8 combinations), including expected X
  cover property (@(*)) (A==0 && B==0 && C_N==1 && X==0);
  cover property (@(*)) (A==1 && B==0 && C_N==1 && X==1);
  cover property (@(*)) (A==0 && B==1 && C_N==1 && X==1);
  cover property (@(*)) (A==0 && B==0 && C_N==0 && X==1);
  cover property (@(*)) (A==1 && B==1 && C_N==1 && X==1);
  cover property (@(*)) (A==1 && B==0 && C_N==0 && X==1);
  cover property (@(*)) (A==0 && B==1 && C_N==0 && X==1);
  cover property (@(*)) (A==1 && B==1 && C_N==0 && X==1);

  // Output activity coverage
  cover property (@(*)) $rose(X));
  cover property (@(*)) $fell(X));

endmodule

// Bind into the DUT to access ports and internal nets
bind sky130_fd_sc_ms__or3b sky130_fd_sc_ms__or3b_sva u_or3b_sva (
  .A        (A),
  .B        (B),
  .C_N      (C_N),
  .X        (X),
  .not0_out (not0_out),
  .or0_out_X(or0_out_X)
);