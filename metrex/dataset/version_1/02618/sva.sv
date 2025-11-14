// SVA for sky130_fd_sc_ls__o221a
// Function: X = (A1 | A2) & (B1 | B2) & C1

module sky130_fd_sc_ls__o221a_sva (
  input logic X,
  input logic A1, A2, B1, B2, C1
);

  // Core functional equivalence (4-state aware)
  property p_func_equiv;
    X === ((A1 | A2) & (B1 | B2) & C1);
  endproperty
  assert property (@(A1 or A2 or B1 or B2 or C1 or X) p_func_equiv);

  // If all inputs are known, output must be known
  property p_known_out_when_known_in;
    !$isunknown({A1,A2,B1,B2,C1}) |-> !$isunknown(X);
  endproperty
  assert property (@(A1 or A2 or B1 or B2 or C1 or X) p_known_out_when_known_in);

  // Basic functional coverage

  // X==1 via each input combination selecting one leg from each OR
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) C1 &&  A1 && !A2 &&  B1 && !B2 && X);
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) C1 &&  A1 && !A2 && !B1 &&  B2 && X);
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) C1 && !A1 &&  A2 &&  B1 && !B2 && X);
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) C1 && !A1 &&  A2 && !B1 &&  B2 && X);

  // X==0 for each gating reason
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) !C1 && (A1||A2) && (B1||B2) && !X);
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) C1 && !(A1||A2) && (B1||B2) && !X);
  cover property (@(A1 or A2 or B1 or B2 or C1 or X) C1 && (A1||A2) && !(B1||B2) && !X);

  // Unknown propagation example: unknown in B-group propagates to X
  cover property (@(A1 or A2 or B1 or B2 or C1 or X)
                  C1 && (A1||A2) && $isunknown(B1) && !B2 && $isunknown(X));

endmodule

bind sky130_fd_sc_ls__o221a sky130_fd_sc_ls__o221a_sva sva_i (.*);