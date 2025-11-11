// SVA checker and binds for sky130_fd_sc_h__a2bb2o_1 and its wrapper

checker a2bb2o_chk (input logic X, A1_N, A2_N, B1, B2);

  // Functional equivalence (4-state accurate)
  assert property ( X === ((A1_N & A2_N) | (B1 & B2)) )
    else $error("X != (A1_N & A2_N) | (B1 & B2)");

  // Output must be known when inputs are known
  assert property ( !$isunknown({A1_N,A2_N,B1,B2}) |-> !$isunknown(X) )
    else $error("X is X/Z while inputs are known");

  // Dominance/consistency checks
  assert property ( ((A1_N & A2_N) === 1'b1) |-> X === 1'b1 );
  assert property ( ((B1 & B2)   === 1'b1) |-> X === 1'b1 );
  assert property ( (((A1_N & A2_N) === 1'b0) && ((B1 & B2) === 1'b0)) |-> X === 1'b0 );

  // Functional coverage of key modes
  cover property ( (A1_N & A2_N) && !(B1 & B2) && (X === 1'b1) ); // A-path only
  cover property ( (B1 & B2)   && !(A1_N & A2_N) && (X === 1'b1) ); // B-path only
  cover property ( (A1_N & A2_N) && (B1 & B2) && (X === 1'b1) );    // both paths
  cover property ( ~((A1_N & A2_N) | (B1 & B2)) && (X === 1'b0) );  // neither path

endchecker

bind sky130_fd_sc_h__a2bb2o_1 a2bb2o_chk a2bb2o_chk_cell (.X(X), .A1_N(A1_N), .A2_N(A2_N), .B1(B1), .B2(B2));
bind my_AND_gate          a2bb2o_chk a2bb2o_chk_wrap (.X(X), .A1_N(A1_N), .A2_N(A2_N), .B1(B1), .B2(B2));