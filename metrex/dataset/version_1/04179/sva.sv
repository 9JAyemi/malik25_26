// SVA for sky130_fd_sc_hd__a211oi
// Function: Y = ~((A1 & A2) | B1 | C1)

module sky130_fd_sc_hd__a211oi_sva (
  input logic Y,
  input logic A1, A2, B1, C1
);

  default clocking cb @($global_clock); endclocking

  // Functional equivalence for known inputs
  assert property ( !$isunknown({A1,A2,B1,C1})
                    |-> (Y == ~((A1 & A2) | B1 | C1)) );

  // No spurious X on output (only if some input is X/Z)
  assert property ( $isunknown(Y) |-> $isunknown({A1,A2,B1,C1}) );

  // Dominating inputs
  assert property ( B1 |-> (Y == 1'b0) );
  assert property ( C1 |-> (Y == 1'b0) );

  // Output high when B1=C1=0 and at least one of A inputs is 0
  assert property ( ~B1 && ~C1 && (~A1 || ~A2) |-> (Y == 1'b1) );

  // Output low when B1=C1=0 and A1&A2=1
  assert property ( ~B1 && ~C1 &&  A1 &&  A2  |-> (Y == 1'b0) );

  // Basic functional coverage
  cover property (Y == 1'b1);
  cover property (Y == 1'b0);
  cover property ($rose(Y));
  cover property ($fell(Y));

  // Input activity coverage
  cover property ($rose(A1));
  cover property ($rose(A2));
  cover property ($rose(B1));
  cover property ($rose(C1));

  // Cause-oriented coverage
  cover property (~B1 && ~C1 && ~A1 &&  Y);
  cover property (~B1 && ~C1 && ~A2 &&  Y);
  cover property ( B1 && !Y);
  cover property ( C1 && !Y);
  cover property (~B1 && ~C1 &&  A1 && A2 && !Y);

endmodule

bind sky130_fd_sc_hd__a211oi sky130_fd_sc_hd__a211oi_sva sva_i (.*);