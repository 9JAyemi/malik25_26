// SVA for sky130_fd_sc_hd__and2b
// Function: X = (~A_N) & B

module sky130_fd_sc_hd__and2b_sva (input logic A_N, B, X);

  // Sample on any input activity; use ##0 to avoid race with 0-delay logic
  default clocking cb @(posedge A_N or negedge A_N or posedge B or negedge B); endclocking

  // Functional equivalence when inputs are known
  property p_func_eq_known;
    (!$isunknown({A_N,B})) |-> ##0 (X === ((~A_N) & B));
  endproperty
  assert property (p_func_eq_known)
    else $error("and2b func mismatch: X=%b A_N=%b B=%b", X, A_N, B);

  // Output known whenever inputs known
  property p_known_out_when_known_in;
    (!$isunknown({A_N,B})) |-> ##0 !$isunknown(X);
  endproperty
  assert property (p_known_out_when_known_in)
    else $error("and2b X is X/Z with known inputs: X=%b A_N=%b B=%b", X, A_N, B);

  // Controlling values (strong one-sided checks even with X on the other input)
  assert property ( (B === 1'b0) |-> ##0 (X === 1'b0) )
    else $error("and2b: B=0 should force X=0");
  assert property ( (A_N === 1'b1) |-> ##0 (X === 1'b0) )
    else $error("and2b: A_N=1 should force X=0");

  // Only condition for X=1
  assert property ( (X === 1'b1) |-> (A_N === 1'b0 && B === 1'b1) )
    else $error("and2b: X=1 requires A_N=0 and B=1");

  // Basic functional covers (truth table)
  cover property ( ##0 (A_N===1'b0 && B===1'b0 && X===1'b0) );
  cover property ( ##0 (A_N===1'b0 && B===1'b1 && X===1'b1) );
  cover property ( ##0 (A_N===1'b1 && B===1'b0 && X===1'b0) );
  cover property ( ##0 (A_N===1'b1 && B===1'b1 && X===1'b0) );

  // Toggle coverage on X
  cover property ( $rose(X) );
  cover property ( $fell(X) );

endmodule

// Bind into DUT
bind sky130_fd_sc_hd__and2b sky130_fd_sc_hd__and2b_sva u_and2b_sva (.A_N(A_N), .B(B), .X(X));