// SVA checker for output_mux
module output_mux_sva (
  input logic A1, A2, B1, C1,
  input logic X,
  input logic VPWR, VGND
);

  // Power rails must be valid
  assert property (@(VPWR or VGND)
                   (VPWR === 1'b1) && (VGND === 1'b0))
    else $error("output_mux: Power rails invalid");

  // Functional equivalence (combinational, zero-latency)
  assert property (@(A1 or A2 or B1 or C1 or X)
                   disable iff ($isunknown({A1,A2,B1,C1}))
                   X === ((A1 & A2) ? B1 : ((A1 & ~A2) ? C1 : 1'b0)))
    else $error("output_mux: X != expected function");

  // No X/Z on X when inputs are known
  assert property (@(A1 or A2 or B1 or C1 or X)
                   disable iff ($isunknown({A1,A2,B1,C1}))
                   !$isunknown(X))
    else $error("output_mux: X is X/Z with known inputs");

  // Stability: if inputs are stable, X must be stable
  assert property (@(A1 or A2 or B1 or C1 or X)
                   disable iff ($isunknown({A1,A2,B1,C1}))
                   $stable({A1,A2,B1,C1}) |-> $stable(X))
    else $error("output_mux: X changed without input change");

  // Non-interference: unselected inputs cannot affect X (with select stable)
  assert property (@(A1 or A2 or B1 or C1 or X)
                   disable iff ($isunknown({A1,A2,B1,C1}))
                   (A1 &&  A2 && $stable({A1,A2,B1}) && $changed(C1)) |-> $stable(X))
    else $error("output_mux: C1 affected X while B1 selected");

  assert property (@(A1 or A2 or B1 or C1 or X)
                   disable iff ($isunknown({A1,A2,B1,C1}))
                   (A1 && !A2 && $stable({A1,A2,C1}) && $changed(B1)) |-> $stable(X))
    else $error("output_mux: B1 affected X while C1 selected");

  assert property (@(A1 or A2 or B1 or C1 or X)
                   disable iff ($isunknown({A1,A2,B1,C1}))
                   (!A1 && $stable(A1) &&
                    ($changed(A2) || $changed(B1) || $changed(C1))) |-> $stable(X))
    else $error("output_mux: Inputs affected X while forced-0 path selected");

  // Coverage: exercise all select paths and transitions
  cover property (@(A1 or A2 or B1 or C1 or X)
                  ! $isunknown({A1,A2,B1,C1}) && A1 &&  A2 && (X==B1));

  cover property (@(A1 or A2 or B1 or C1 or X)
                  ! $isunknown({A1,A2,B1,C1}) && A1 && !A2 && (X==C1));

  cover property (@(A1 or A2 or B1 or C1 or X)
                  ! $isunknown({A1,A2,B1,C1}) && !A1 && (X==1'b0));

  // Transition between C1-path and B1-path with differing data
  cover property (@(A1 or A2 or B1 or C1 or X)
                  ! $isunknown({A1,A2,B1,C1}) &&
                  A1 && !A2 && (B1!=C1) ##1 A1 && A2 && (X==B1));

  cover property (@(A1 or A2 or B1 or C1 or X)
                  ! $isunknown({A1,A2,B1,C1}) &&
                  A1 && A2 && (B1!=C1) ##1 A1 && !A2 && (X==C1));

endmodule

// Bind into the DUT
bind output_mux output_mux_sva u_output_mux_sva (
  .A1(A1), .A2(A2), .B1(B1), .C1(C1),
  .X(X), .VPWR(VPWR), .VGND(VGND)
);