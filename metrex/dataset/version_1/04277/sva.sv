// SVA for mux_4to2
module mux_4to2_sva (
  input logic X,
  input logic A0, A1, A2, A3,
  input logic S0, S1
);

  // Sample on any edge of inputs/selects
  default clocking cb @(
    posedge A0 or negedge A0 or
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge S0 or negedge S0 or
    posedge S1 or negedge S1
  ); endclocking

  // Functional equivalence (golden equation)
  assert property (
    X === ((S1 & S0 & A3) | (~S1 & S0 & A2) | (S1 & ~S0 & A1) | (~S1 & ~S0 & A0))
  ) else $error("mux_4to2: functional mismatch");

  // Data change must propagate to X when selected (same-sample responsiveness)
  assert property ( ({S1,S0}==2'b00 && $changed(A0)) |-> $changed(X) );
  assert property ( ({S1,S0}==2'b01 && $changed(A2)) |-> $changed(X) );
  assert property ( ({S1,S0}==2'b10 && $changed(A1)) |-> $changed(X) );
  assert property ( ({S1,S0}==2'b11 && $changed(A3)) |-> $changed(X) );

  // Functional coverage: each select path observed with correct mapping
  cover property ( ({S1,S0}==2'b00) && (X===A0) );
  cover property ( ({S1,S0}==2'b01) && (X===A2) );
  cover property ( ({S1,S0}==2'b10) && (X===A1) );
  cover property ( ({S1,S0}==2'b11) && (X===A3) );

  // Cover that select changes can affect X (at least once)
  cover property ( $changed({S1,S0}) && $changed(X) );

endmodule

// Bind into DUT
bind mux_4to2 mux_4to2_sva mux_4to2_sva_i (
  .X(X), .A0(A0), .A1(A1), .A2(A2), .A3(A3), .S0(S0), .S1(S1)
);