// SVA for sky130_fd_sc_lp__or4bb
// Function: X = A | B | ~C_N | ~D_N

module sky130_fd_sc_lp__or4bb_sva
(
  input logic A,
  input logic B,
  input logic C_N,
  input logic D_N,
  input logic X
);

  // Clock on any input change
  default clocking cb @(A or B or C_N or D_N); endclocking
  // Guard for known inputs
  function automatic bit known_inputs(); return !$isunknown({A,B,C_N,D_N}); endfunction

  // X must be known when inputs are known
  assert property (disable iff (!known_inputs()) ##0 !$isunknown(X))
    else $error("X is X/Z with known inputs");

  // Functional equivalence (after delta to allow settle)
  assert property (disable iff (!known_inputs()) ##0 (X == (A | B | ~C_N | ~D_N)))
    else $error("Functional mismatch: X != A|B|~C_N|~D_N");

  // Dominance: any asserting literal must force X=1
  assert property (disable iff (!known_inputs()) A   |-> ##0 (X==1'b1));
  assert property (disable iff (!known_inputs()) B   |-> ##0 (X==1'b1));
  assert property (disable iff (!known_inputs()) !C_N |-> ##0 (X==1'b1));
  assert property (disable iff (!known_inputs()) !D_N |-> ##0 (X==1'b1));

  // Only-zero case
  assert property (disable iff (!known_inputs())
                   (!A && !B && C_N && D_N) |-> ##0 (X==1'b0));

  // Minimal, high-value functional coverage
  cover property (known_inputs() && ( A && !B &&  C_N &&  D_N) && (X==1)); // A drives
  cover property (known_inputs() && (!A &&  B &&  C_N &&  D_N) && (X==1)); // B drives
  cover property (known_inputs() && (!A && !B && !C_N &&  D_N) && (X==1)); // ~C_N drives
  cover property (known_inputs() && (!A && !B &&  C_N && !D_N) && (X==1)); // ~D_N drives
  cover property (known_inputs() && (!A && !B &&  C_N &&  D_N) && (X==0)); // only-zero case

  // Output transitions (with known inputs)
  cover property (known_inputs() && $rose(X));
  cover property (known_inputs() && $fell(X));

endmodule

// Bind into the DUT
bind sky130_fd_sc_lp__or4bb sky130_fd_sc_lp__or4bb_sva u_sva (
  .A(A), .B(B), .C_N(C_N), .D_N(D_N), .X(X)
);