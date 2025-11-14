// SVA for sky130_fd_sc_ls__or3b: X = A | B | ~C_N
// Bind this checker to the DUT instance(s).

module sky130_fd_sc_ls__or3b_sva
(
  input logic A,
  input logic B,
  input logic C_N,
  input logic X
);

  // Sample on any input edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C_N or negedge C_N
  ); endclocking

  // Core functional equivalence (when inputs are known)
  property p_func_known;
    !$isunknown({A,B,C_N}) |-> (X === (A | B | ~C_N));
  endproperty
  assert property (p_func_known);

  // Output must be known when inputs are known
  assert property ( !$isunknown({A,B,C_N}) |-> !$isunknown(X) );

  // Dominating conditions
  assert property ( A    == 1'b1 |-> X == 1'b1 );
  assert property ( B    == 1'b1 |-> X == 1'b1 );
  assert property ( C_N  == 1'b0 |-> X == 1'b1 );
  assert property ( A==1'b0 && B==1'b0 && C_N==1'b1 |-> X == 1'b0 );

  // Functional coverage: all input combinations with expected X
  cover property ( A==0 && B==0 && C_N==0 && X==1 );
  cover property ( A==0 && B==0 && C_N==1 && X==0 );
  cover property ( A==0 && B==1 && C_N==0 && X==1 );
  cover property ( A==0 && B==1 && C_N==1 && X==1 );
  cover property ( A==1 && B==0 && C_N==0 && X==1 );
  cover property ( A==1 && B==0 && C_N==1 && X==1 );
  cover property ( A==1 && B==1 && C_N==0 && X==1 );
  cover property ( A==1 && B==1 && C_N==1 && X==1 );

  // Sensitivity covers: each single-input toggle can control X when others deasserted
  cover property ( A==0 && B==0 && C_N==1 ##1 A==1 && X==1 );
  cover property ( A==0 && B==0 && C_N==1 ##1 B==1 && X==1 );
  cover property ( A==0 && B==0 && C_N==1 ##1 C_N==0 && X==1 );
  cover property ( A==0 && B==0 && C_N==0 && X==1 ##1 C_N==1 && X==0 );

endmodule

// Bind to DUT
bind sky130_fd_sc_ls__or3b sky130_fd_sc_ls__or3b_sva or3b_sva_bind (
  .A(A), .B(B), .C_N(C_N), .X(X)
);