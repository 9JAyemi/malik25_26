// SVA checker for logic_circuit
module logic_circuit_sva (
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

  // Expected function (simplified from DUT SOP)
  function automatic logic exp (logic A1_N, logic A2_N, logic B1, logic B2);
    // Y = (B1 | A1_N | !A2_N | B2) & (B1 | !A1_N | A2_N)
    exp = (B1 | A1_N | ~A2_N | B2) & (B1 | ~A1_N | A2_N);
  endfunction

  // Convenience event: fire on any input transition
  `define CHG_EVENT (A1_N or A2_N or B1 or B2)

  // Functional equivalence on known inputs
  assert property (@(`CHG_EVENT)
    !$isunknown({A1_N,A2_N,B1,B2}) |-> (Y == exp(A1_N,A2_N,B1,B2))
  ) else $error("logic_circuit: Y mismatches expected function");

  // Knownness: known inputs imply known output
  assert property (@(`CHG_EVENT)
    !$isunknown({A1_N,A2_N,B1,B2}) |-> !$isunknown(Y)
  ) else $error("logic_circuit: Y is X/Z with known inputs");

  // Key directional invariants (helpful, concise)
  // If B1=1 then Y=1
  assert property (@(`CHG_EVENT)
    (!$isunknown(B1) && B1) |-> Y
  ) else $error("logic_circuit: B1=1 must force Y=1");

  // If A1_N==A2_N (both 0 or both 1) then Y=1
  assert property (@(`CHG_EVENT)
    (!$isunknown({A1_N,A2_N}) && (A1_N === A2_N)) |-> Y
  ) else $error("logic_circuit: A1_N==A2_N must force Y=1");

  // Corner zeros
  // A1_N=1, A2_N=0, B1=0 => Y=0 (any B2)
  assert property (@(`CHG_EVENT)
    (!$isunknown({A1_N,A2_N,B1}) &&  A1_N && !A2_N && !B1) |-> !Y
  ) else $error("logic_circuit: A1_N=1,A2_N=0,B1=0 must force Y=0");

  // A1_N=0, A2_N=1, B1=0, B2=0 => Y=0
  assert property (@(`CHG_EVENT)
    (!$isunknown({A1_N,A2_N,B1,B2}) && !A1_N &&  A2_N && !B1 && !B2) |-> !Y
  ) else $error("logic_circuit: !A1_N,A2_N, !B1,!B2 must force Y=0");

  // Coverage
  // 1) Exercise all 16 input combinations and check correct Y
  genvar v;
  for (v = 0; v < 16; v++) begin : C_VEC
    localparam logic [3:0] VEC = v[3:0]; // {A1_N,A2_N,B1,B2}
    cover property (@(`CHG_EVENT)
      {A1_N,A2_N,B1,B2} == VEC && (Y == exp(A1_N,A2_N,B1,B2))
    );
  end

  // 2) Y edges
  cover property (@(posedge Y));
  cover property (@(negedge Y));

  `undef CHG_EVENT
endmodule

// Bind into the DUT
bind logic_circuit logic_circuit_sva i_logic_circuit_sva(.*);