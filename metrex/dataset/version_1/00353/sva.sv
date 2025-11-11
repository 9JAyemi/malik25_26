// SVA checker for four_input_module
// Bind this checker to the DUT to verify behavior and get coverage

module four_input_module_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic C1,
  input logic X
);

  // Concurrent assertions sample on a global clock
  default clocking cb @(posedge $global_clock); endclocking

  // No X/Zs on key signals
  assert property ( !$isunknown({A1,A2,B1,C1,X}) );

  // Functional equivalence (concurrent)
  assert property ( X == ((A1 && A2) || (!A1 && !B1 && C1)) );

  // Branch-level checks (priority and outcomes)
  assert property ( (A1 && A2) |-> X );
  assert property ( (!A1 && B1) |-> !X );
  assert property ( (!A1 && !B1 && C1) |-> X );
  assert property ( (!(A1 && A2) && !(!A1 && B1) && !(!A1 && !B1 && C1)) |-> !X );

  // Delta-cycle accurate functional check
  always_comb
    assert ( X === ((A1 & A2) | (~A1 & ~B1 & C1)) )
      else $error("X mismatch: A1=%0b A2=%0b B1=%0b C1=%0b X=%0b", A1, A2, B1, C1, X);

  // Coverage: exercise all paths and both output polarities and toggles
  cover property ( (A1 && A2) && X );
  cover property ( (!A1 && B1) && !X );
  cover property ( (!A1 && !B1 && C1) && X );
  cover property ( (!(A1 && A2) && !(!A1 && B1) && !(!A1 && !B1 && C1)) && !X );
  cover property ( !X ##1 X );
  cover property ( X ##1 !X );

endmodule

// Bind into the DUT
bind four_input_module four_input_module_sva sva_inst (
  .A1(A1), .A2(A2), .B1(B1), .C1(C1), .X(X)
);