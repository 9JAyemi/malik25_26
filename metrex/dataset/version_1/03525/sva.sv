// SVA bind module for sky130_fd_sc_hd__or4b
module sky130_fd_sc_hd__or4b_sva (
  input logic A, B, C, D_N, X
);
  default clocking cb @(*); endclocking

  // Functional correctness for known inputs
  assert property ( !$isunknown({A,B,C,D_N}) |-> (X == ~(A & B & C & D_N)) );

  // Output semantics
  assert property ( !X |-> (A && B && C && D_N) );
  assert property ( (!A || !B || !C || !D_N) |-> (X == 1'b1) );

  // No spurious output changes
  assert property ( $changed(X) |-> $changed({A,B,C,D_N}) );

  // Output is known when inputs are known
  assert property ( !$isunknown({A,B,C,D_N}) |-> !$isunknown(X) );

  // Functional coverage (key corners)
  cover property ( A && B && C && D_N && (X == 1'b0) );           // all ones -> 0
  cover property ( !A &&  B &&  C &&  D_N && (X == 1'b1) );       // single zero on A
  cover property (  A && !B &&  C &&  D_N && (X == 1'b1) );       // single zero on B
  cover property (  A &&  B && !C &&  D_N && (X == 1'b1) );       // single zero on C
  cover property (  A &&  B &&  C && !D_N && (X == 1'b1) );       // single zero on D_N
  cover property ( !A && !B && !C && !D_N && (X == 1'b1) );       // all zeros -> 1
endmodule

// Bind into DUT
bind sky130_fd_sc_hd__or4b sky130_fd_sc_hd__or4b_sva i_sva (.*);