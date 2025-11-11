// SVA for sky130_fd_sc_ms__a221o
// Function: X = (A1 & A2) | (B1 & B2) | C1

module sky130_fd_sc_ms__a221o_sva (
  input  logic A1, A2, B1, B2, C1,
  input  logic X,
  input  logic and0_out, and1_out, or0_out_X
);
  // local helpers
  wire tA = A1 & A2;
  wire tB = B1 & B2;
  wire tC = C1;

  // Functional equivalence (post-delta to allow 0-delay propagation)
  assert property (@(A1 or A2 or B1 or B2 or C1 or X) ##0
                   X === (tA | tB | tC))
    else $error("X functional mismatch");

  // Knownness when inputs are known
  assert property (@(A1 or A2 or B1 or B2 or C1) ##0
                   !$isunknown({A1,A2,B1,B2,C1}) |-> (X == (tA | tB | tC)))
    else $error("X not deterministically derived from known inputs");

  // Structural checks of internal nets
  assert property (@(A1 or A2 or and1_out) ##0 and1_out === tA)
    else $error("and1_out != A1&A2");
  assert property (@(B1 or B2 or and0_out) ##0 and0_out === tB)
    else $error("and0_out != B1&B2");
  assert property (@(and1_out or and0_out or C1 or or0_out_X) ##0
                   or0_out_X === (and1_out | and0_out | C1))
    else $error("or0_out_X != and1_out|and0_out|C1");
  assert property (@(or0_out_X or X) ##0 X === or0_out_X)
    else $error("X != or0_out_X (buf)");

  // Knownness of internal nets when inputs are known
  assert property (@(A1 or A2) ##0 !$isunknown({A1,A2}) |-> !($isunknown(and1_out)))
    else $error("and1_out unknown with known A1/A2");
  assert property (@(B1 or B2) ##0 !$isunknown({B1,B2}) |-> !($isunknown(and0_out)))
    else $error("and0_out unknown with known B1/B2");
  assert property (@(A1 or A2 or B1 or B2 or C1) ##0
                   !$isunknown({A1,A2,B1,B2,C1}) |-> !($isunknown(or0_out_X)))
    else $error("or0_out_X unknown with known inputs");

  // Compact functional coverage (trigger on any input change, sample after delta)
  // A-only, B-only, C-only drive X=1
  cover property (@(A1 or A2 or B1 or B2 or C1) ##0
                  !$isunknown({A1,A2,B1,B2,C1}) &&  tA && !tB && !tC && X);
  cover property (@(A1 or A2 or B1 or B2 or C1) ##0
                  !$isunknown({A1,A2,B1,B2,C1}) && !tA &&  tB && !tC && X);
  cover property (@(A1 or A2 or B1 or B2 or C1) ##0
                  !$isunknown({A1,A2,B1,B2,C1}) && !tA && !tB &&  tC && X);
  // None true => X=0
  cover property (@(A1 or A2 or B1 or B2 or C1) ##0
                  !$isunknown({A1,A2,B1,B2,C1}) && !tA && !tB && !tC && !X);
  // Multiple terms true
  cover property (@(A1 or A2 or B1 or B2 or C1) ##0
                  !$isunknown({A1,A2,B1,B2,C1}) &&  tA &&  tB && !tC && X);
  cover property (@(A1 or A2 or B1 or B2 or C1) ##0
                  !$isunknown({A1,A2,B1,B2,C1}) &&  tA &&  tB &&  tC && X);
endmodule

// Bind into DUT (accesses internal nets)
bind sky130_fd_sc_ms__a221o sky130_fd_sc_ms__a221o_sva u_a221o_sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .X(X),
  .and0_out(and0_out), .and1_out(and1_out), .or0_out_X(or0_out_X)
);