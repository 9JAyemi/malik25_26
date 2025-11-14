// SVA for five_input_gate
// Bind into the DUT to check functional correctness, priority behavior,
// X-propagation discipline, and provide concise coverage.

module five_input_gate_sva;
  // Sample on any relevant signal change; check after ##0 to allow settle
  default clocking cb @(A1 or A2 or B1 or B2 or C1 or X); endclocking

  // Functional equivalence (under known inputs)
  property p_eq;
    (!$isunknown({A1,A2,B1,B2,C1})) |-> ##0
      (X == (A1 | (!A2 & ((B1 & B2) | (!C1)))));
  endproperty
  a_eq: assert property (p_eq);

  // Priority/short-circuit checks
  a_p1: assert property ( A1 |-> ##0 (X == 1'b1) );
  a_p2: assert property ( !A1 && A2 |-> ##0 (X == 1'b0) );
  a_p3: assert property ( !A1 && !A2 && B1 && B2 |-> ##0 (X == 1'b1) );
  a_p4: assert property ( !A1 && !A2 && !(B1 && B2) |-> ##0 (X == !C1) );

  // X known if inputs are known
  a_known:  assert property ( (!$isunknown({A1,A2,B1,B2,C1})) |-> ##0 !$isunknown(X) );

  // No unintended memory: if inputs hold, output holds
  a_stable: assert property ( $stable({A1,A2,B1,B2,C1}) |-> ##0 $stable(X) );

  // Coverage: exercise all decision paths and both X edges
  c_p1:   cover property ( A1 ##0 (X==1) );
  c_p2:   cover property ( !A1 && A2 ##0 (X==0) );
  c_p3:   cover property ( !A1 && !A2 && B1 && B2 ##0 (X==1) );
  c_p4a:  cover property ( !A1 && !A2 && !(B1 && B2) && !C1 ##0 (X==1) );
  c_p4b:  cover property ( !A1 && !A2 && !(B1 && B2) &&  C1 ##0 (X==0) );
  c_rose: cover property ( $rose(X) );
  c_fell: cover property ( $fell(X) );
endmodule

bind five_input_gate five_input_gate_sva sva();