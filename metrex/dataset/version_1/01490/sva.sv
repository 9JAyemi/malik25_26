// SVA checker for combinational_circuit
module combinational_circuit_sva (
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic Y
);

  // Sample on any clean edge of inputs; evaluate consequents after design settles
  default clocking cb @ (posedge A1 or negedge A1 or
                         posedge A2 or negedge A2 or
                         posedge B1_N or negedge B1_N); endclocking

  // Golden Boolean equivalence (when all inputs are known)
  property p_func_equiv;
    disable iff ($isunknown({A1,A2,B1_N}))
      1'b1 |-> ##0 (Y == ((A1 & A2) | ((~A1 & ~A2) & B1_N)));
  endproperty
  assert property (p_func_equiv);

  // Decomposed checks (also handle B1_N unknown independently where possible)
  property p_11_then_1;
    disable iff ($isunknown({A1,A2}))
      (A1 & A2) |-> ##0 (Y == 1'b1);
  endproperty
  assert property (p_11_then_1);

  property p_one_hot_then_0;
    disable iff ($isunknown({A1,A2}))
      (A1 ^ A2) |-> ##0 (Y == 1'b0);
  endproperty
  assert property (p_one_hot_then_0);

  property p_00_then_B1N;
    disable iff ($isunknown({A1,A2,B1_N}))
      (~A1 & ~A2) |-> ##0 (Y == B1_N);
  endproperty
  assert property (p_00_then_B1N);

  // Y must be known when domain decided by A1/A2 (independent of B1_N)
  property p_known_when_any_high;
    disable iff ($isunknown({A1,A2}))
      (A1 | A2) |-> ##0 (!$isunknown(Y) && (Y == (A1 & A2)));
  endproperty
  assert property (p_known_when_any_high);

  // Functional coverage of all input cases (and expected Y)
  cover property ((~A1 & ~A2 & ~B1_N) ##0 (Y == 1'b0));
  cover property ((~A1 & ~A2 &  B1_N) ##0 (Y == 1'b1));
  cover property (( A1 & ~A2)         ##0 (Y == 1'b0));
  cover property ((~A1 &  A2)         ##0 (Y == 1'b0));
  cover property (( A1 &  A2)         ##0 (Y == 1'b1));

endmodule

// Bind the checker to the DUT
bind combinational_circuit combinational_circuit_sva sva_i (
  .A1(A1), .A2(A2), .B1_N(B1_N), .Y(Y)
);