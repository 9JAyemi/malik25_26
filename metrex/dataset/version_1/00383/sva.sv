// SVA checker for sky130_fd_sc_lp__xnor2
// Focus: concise, high-value checks + functional coverage

// Bind this checker to the DUT
bind sky130_fd_sc_lp__xnor2 xnor2_sva u_xnor2_sva (
  .A(A), .B(B), .Y(Y),
  .n1(n1), .n2(n2), .n3(n3), .n4(n4),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);

module xnor2_sva (
  input logic A, B, Y,
  input logic n1, n2, n3, n4,
  input logic VPWR, VGND, VPB, VNB
);
  default clocking cb @ (posedge $global_clock); endclocking

  // Helper
  function automatic bit known2(logic a, logic b);
    return (!$isunknown(a) && !$isunknown(b));
  endfunction

  // Functional correctness for known inputs: Y == XNOR(A,B)
  property p_func_xnor_known;
    (known2(A,B)) |-> (Y === (A ~^ B));
  endproperty
  assert property (p_func_xnor_known);

  // Structural/dataflow consistency (checked after updates via ##0)
  // Ensures internal transforms and final output match the netlist
  property p_struct_relations;
    1 |-> ##0 ( n1 === ~(A & B)
             && n2 === ~(A | B)
             && n3 === ~(n1 | n2)
             && n4 === ~n3
             && Y  === n4 );
  endproperty
  // Trigger on any relevant activity to recheck in steady state
  assert property (@(A or B or n1 or n2 or n3 or n4) p_struct_relations);

  // Output never high-impedance
  assert property (@(Y) ##0 (Y !== 1'bz));

  // Output changes only if an input changed across a sample
  assert property ( (Y !== $past(Y)) |-> ($changed(A) || $changed(B)) );

  // Power rails must remain at proper constants
  assert property (@(VPWR or VGND or VPB or VNB)
                   ##0 (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0));

  // -------------------
  // Coverage
  // -------------------
  // Truth table points (for known inputs)
  cover property (known2(A,B) && A==1'b0 && B==1'b0 && Y==1'b1);
  cover property (known2(A,B) && A==1'b0 && B==1'b1 && Y==1'b0);
  cover property (known2(A,B) && A==1'b1 && B==1'b0 && Y==1'b0);
  cover property (known2(A,B) && A==1'b1 && B==1'b1 && Y==1'b1);

  // Output transitions observed
  cover property ($rose(Y));
  cover property ($fell(Y));

  // Behavioral transitions: equal->not equal and not equal->equal
  cover property ( known2(A,B) && (A==B) ##1 known2(A,B) && (A!=B) && (Y==1'b0) );
  cover property ( known2(A,B) && (A!=B) ##1 known2(A,B) && (A==B) && (Y==1'b1) );

endmodule