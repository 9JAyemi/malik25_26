// SVA checker for my_circuit
`ifndef MY_CIRCUIT_SVA
`define MY_CIRCUIT_SVA

module my_circuit_sva (
  input logic A1, A2, A3, B1,
  input logic Y,
  input logic VPWR, VGND, VPB, VNB
);

  // Event for combinational sampling
  `define COMB_EV (posedge A1 or negedge A1 or \
                    posedge A2 or negedge A2 or \
                    posedge A3 or negedge A3 or \
                    posedge B1 or negedge B1 or \
                    posedge Y  or negedge Y)

  function automatic int unsigned pop3 (input logic a,b,c);
    return a + b + c;
  endfunction

  logic a_and, a_or, expected_y, bug_term;
  assign a_and      = A1 & A2 & A3;
  assign a_or       = A1 | A2 | A3;
  assign expected_y = B1 | a_and;
  assign bug_term   = ((a_or - a_and) >= 2'b10);

  // Functional equivalence to implemented RTL (concise complete check)
  always_comb
    assert (Y === expected_y)
      else $error("my_circuit: Y mismatch: Y=%0b expected=%0b A1=%0b A2=%0b A3=%0b B1=%0b",
                  Y, expected_y, A1, A2, A3, B1);

  // Power/ground sanity (rails should be correct constants)
  always_comb
    assert (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0)
      else $error("my_circuit: power pins not at expected rails VPWR=%b VGND=%b VPB=%b VNB=%b",
                  VPWR, VGND, VPB, VNB);

  // No X/Z on Y when inputs are known
  always_comb
    if (!$isunknown({A1,A2,A3,B1}))
      assert (!$isunknown(Y))
        else $error("my_circuit: Y is X/Z with known inputs");

  // Width/compare term is unreachable (documents/guards design intent)
  always_comb
    assert (!bug_term)
      else $error("my_circuit: (A_or - A_and) >= 2'b10 evaluated true unexpectedly");

  // Targeted implications (redundant to functional check but diagnostic)
  property p_b1_forces_one; B1 |-> Y; endproperty
  assert property (@`COMB_EV p_b1_forces_one);

  property p_allAs_force_one; (!B1 && a_and) |-> Y; endproperty
  assert property (@`COMB_EV p_allAs_force_one);

  property p_else_zero; (!B1 && !a_and) |-> !Y; endproperty
  assert property (@`COMB_EV p_else_zero);

  // Coverage (exercise key corners, including the "two-ones" case)
  cover property (@`COMB_EV (B1 && Y));
  cover property (@`COMB_EV (!B1 && a_and && Y));
  cover property (@`COMB_EV (!B1 && pop3(A1,A2,A3)==0 && !Y));
  cover property (@`COMB_EV (!B1 && pop3(A1,A2,A3)==1 && !Y));
  cover property (@`COMB_EV (!B1 && pop3(A1,A2,A3)==2 && !Y)); // shows non-majority behavior
  cover property (@`COMB_EV ($rose(Y)));
  cover property (@`COMB_EV ($fell(Y)));

endmodule

// Bind into all instances of my_circuit
bind my_circuit my_circuit_sva u_my_circuit_sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .Y(Y),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);

`endif