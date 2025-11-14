// SVA for four_in_one_out
// Bindable, concise, and functionally strong

module four_in_one_out_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic B2,
  input logic X
);

  // Clock on any input edge (combinational sampling)
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2
  ); endclocking

  // Useful lets
  let parity3 = (A2 ^ B1 ^ B2);
  let cnt4    = $countones({A1, A2, B1, B2});

  // Core functional equivalence (derived from RTL):
  // X == (~A2) when A1==1; else X == (A2 ^ B1 ^ B2)
  assert property ( !$isunknown({A1,A2,B1,B2}) |->
                    X == (A1 ? ~A2 : parity3) )
    else $error("four_in_one_out: functional mismatch");

  // Output must be known when inputs are known
  assert property ( !$isunknown({A1,A2,B1,B2}) |-> !$isunknown(X) )
    else $error("four_in_one_out: X is X/Z with known inputs");

  // Independence: when A1==1, X must not depend on B1/B2
  assert property ( A1 && !$isunknown({A1,A2,B1,B2,X}) &&
                    $stable(A2) && ($changed(B1) || $changed(B2)) |-> $stable(X) )
    else $error("four_in_one_out: B1/B2 affected X while A1==1");

  // Sensitivity: when A1==0, flipping exactly one of A2/B1/B2 flips X
  assert property ( !A1 && !$isunknown({A1,A2,B1,B2,X}) &&
                    $changed(A2) && $stable(B1) && $stable(B2) |-> $changed(X) )
    else $error("four_in_one_out: A2 toggle did not toggle X when A1==0");
  assert property ( !A1 && !$isunknown({A1,A2,B1,B2,X}) &&
                    $changed(B1) && $stable(A2) && $stable(B2) |-> $changed(X) )
    else $error("four_in_one_out: B1 toggle did not toggle X when A1==0");
  assert property ( !A1 && !$isunknown({A1,A2,B1,B2,X}) &&
                    $changed(B2) && $stable(A2) && $stable(B1) |-> $changed(X) )
    else $error("four_in_one_out: B2 toggle did not toggle X when A1==0");

  // Coverage: exercise both branches and extremes
  cover property ( !A1 && X == parity3 );
  cover property (  A1 && X == ~A2     );
  cover property ( cnt4 == 0 );
  cover property ( cnt4 == 4 );
  cover property ( !A1 && parity3 == 0 && X == 0 );
  cover property ( !A1 && parity3 == 1 && X == 1 );
  cover property (  A1 && A2 == 0 && X == 1 );
  cover property (  A1 && A2 == 1 && X == 0 );

endmodule

bind four_in_one_out four_in_one_out_sva sva_inst (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .X(X)
);