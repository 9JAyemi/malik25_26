// SVA for sky130_fd_sc_ls__o41a: X = (A1 | A2 | A3 | A4) & B1
// Bind this file to the DUT
//   bind sky130_fd_sc_ls__o41a o41a_sva o41a_sva_i (.*);

module o41a_sva (
  input logic X,
  input logic A1, A2, A3, A4,
  input logic B1
);

  // Sample on any edge of inputs or output
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge A4 or negedge A4 or
    posedge B1 or negedge B1 or
    posedge X  or negedge X
  ); endclocking

  // Functional equivalence when inputs are known (2-state check)
  assert property ( !$isunknown({A1,A2,A3,A4,B1})
                    |-> ( X === ((A1|A2|A3|A4) & B1) ) )
    else $error("o41a: functional mismatch with known inputs");

  // Dominating values and X-propagation in 4-state semantics
  // B1=0 forces X=0 regardless of A's (0 is AND-controlling)
  assert property ( (B1 === 1'b0) |-> (X === 1'b0) )
    else $error("o41a: B1=0 did not force X=0");

  // OR term all zero forces X=0 regardless of B1
  assert property ( ((A1===0)&&(A2===0)&&(A3===0)&&(A4===0)) |-> (X===1'b0) )
    else $error("o41a: all A's=0 did not force X=0");

  // If any Ai is 1, OR term is 1 and X follows B1 (including X if B1 is X)
  assert property ( ((A1===1)||(A2===1)||(A3===1)||(A4===1)) |-> (X === B1) )
    else $error("o41a: OR=1 case did not make X follow B1");

  // If B1=1 and no Ai==1 but some Ai unknown, X must be unknown
  assert property ( (B1===1) && !(A1===1||A2===1||A3===1||A4===1) && $isunknown({A1,A2,A3,A4})
                    |-> $isunknown(X) )
    else $error("o41a: X did not become unknown under B1=1 with unknown A's and no asserted A");

  // No spurious X activity without input changes
  assert property ( !$changed({A1,A2,A3,A4,B1}) |-> !$changed(X) )
    else $error("o41a: X changed without any input change");

  // ----------------
  // Functional coverage
  // ----------------

  // Output toggles
  cover property ( $rose(X) );
  cover property ( $fell(X) );

  // Each input toggles
  cover property ( $rose(A1) ); cover property ( $fell(A1) );
  cover property ( $rose(A2) ); cover property ( $fell(A2) );
  cover property ( $rose(A3) ); cover property ( $fell(A3) );
  cover property ( $rose(A4) ); cover property ( $fell(A4) );
  cover property ( $rose(B1) ); cover property ( $fell(B1) );

  // Key functional scenarios
  // B1=0 while some Ai=1 -> X=0
  cover property ( (B1===0) && (A1===1 || A2===1 || A3===1 || A4===1) && (X===0) );

  // B1=1 and exactly one Ai=1 -> X=1 (one-hot cases)
  cover property ( (B1===1)&&(A1===1)&&(A2===0)&&(A3===0)&&(A4===0)&&(X===1) );
  cover property ( (B1===1)&&(A1===0)&&(A2===1)&&(A3===0)&&(A4===0)&&(X===1) );
  cover property ( (B1===1)&&(A1===0)&&(A2===0)&&(A3===1)&&(A4===0)&&(X===1) );
  cover property ( (B1===1)&&(A1===0)&&(A2===0)&&(A3===0)&&(A4===1)&&(X===1) );

  // B1=1 and all Ai=0 -> X=0
  cover property ( (B1===1)&&(A1===0)&&(A2===0)&&(A3===0)&&(A4===0)&&(X===0) );

endmodule

// Bind to the DUT
bind sky130_fd_sc_ls__o41a o41a_sva o41a_sva_i (.*);