// SVA for combinational_circuit
// Concise, high-quality functional checks + coverage

module combinational_circuit_sva (
  input logic A1, A2, A3, B1, B2, X,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any input edge
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2
  ); endclocking

  // Helper: golden combinational function
  function automatic logic exp_x(logic a1, a2, a3, b1, b2);
    exp_x = (a1 == 1'b1) ? b1 : ((a2 == 1'b1) && (a3 == 1'b0)) ? b2 : b1;
  endfunction

  // No-X/Z on interface
  assert property (!$isunknown({A1,A2,A3,B1,B2,X}))
    else $error("X/Z detected on interface signals");

  // Power pins are expected constants (as modeled)
  assert property (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0)
    else $error("Supply pins not at expected constants");

  // Functional equivalence (single, strongest check)
  assert property (X == exp_x(A1,A2,A3,B1,B2))
    else $error("X != expected function of inputs");

  // Corner-case/intent checks (redundant but intent-clarifying)
  assert property (A1 |-> (X == B1))
    else $error("When A1==1, X must equal B1");

  assert property ((!A1 && A2 && !A3) |-> (X == B2))
    else $error("When A1==0 and A2==1 and A3==0, X must equal B2");

  assert property ((!A1 && !(A2 && !A3)) |-> (X == B1))
    else $error("Else case must select B1");

  // Functional coverage (hit each selection path and B1/B2 relation)
  cover property (A1);
  cover property (!A1 && A2 && !A3);
  cover property (!A1 && !(A2 && !A3));
  cover property (B1 != B2);
  cover property (B1 == B2);

endmodule

// Bind into all instances of combinational_circuit
bind combinational_circuit combinational_circuit_sva comb_sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .B2(B2), .X(X),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);