// SVA checker for MUX_4to1. Bind to DUT as shown at bottom.
module MUX_4to1_sva (
  input X0, X1, X2, X3,
  input S0, S1,
  input Y
);

  // Sample on any relevant edge to catch all combinational changes
  default clocking cb @(
      posedge S0 or negedge S0 or
      posedge S1 or negedge S1 or
      posedge X0 or negedge X0 or
      posedge X1 or negedge X1 or
      posedge X2 or negedge X2 or
      posedge X3 or negedge X3 or
      posedge Y  or negedge Y
  ); endclocking

  // Selects must be known (no X/Z)
  a_sel_known: assert property ( !$isunknown({S1,S0}) )
    else $error("MUX_4to1: S1/S0 contain X/Z");

  // Functional correctness per select value (allow X on selected data to propagate)
  a_mux_00: assert property ( ({S1,S0}==2'b00) |-> ##0 (Y === X0) )
    else $error("MUX_4to1: select 00, Y!=X0");
  a_mux_01: assert property ( ({S1,S0}==2'b01) |-> ##0 (Y === X1) )
    else $error("MUX_4to1: select 01, Y!=X1");
  a_mux_10: assert property ( ({S1,S0}==2'b10) |-> ##0 (Y === X2) )
    else $error("MUX_4to1: select 10, Y!=X2");
  a_mux_11: assert property ( ({S1,S0}==2'b11) |-> ##0 (Y === X3) )
    else $error("MUX_4to1: select 11, Y!=X3");

  // No-X leakage when selected input is known
  a_no_x_00: assert property ( ({S1,S0}==2'b00) && !$isunknown(X0) |-> ##0 (Y == X0) )
    else $error("MUX_4to1: X0 known but Y mismatch/unknown");
  a_no_x_01: assert property ( ({S1,S0}==2'b01) && !$isunknown(X1) |-> ##0 (Y == X1) )
    else $error("MUX_4to1: X1 known but Y mismatch/unknown");
  a_no_x_10: assert property ( ({S1,S0}==2'b10) && !$isunknown(X2) |-> ##0 (Y == X2) )
    else $error("MUX_4to1: X2 known but Y mismatch/unknown");
  a_no_x_11: assert property ( ({S1,S0}==2'b11) && !$isunknown(X3) |-> ##0 (Y == X3) )
    else $error("MUX_4to1: X3 known but Y mismatch/unknown");

  // Compact equivalence to the ternary equation (redundant but strong)
  a_equation: assert property ( 1 |-> ##0
    ( Y === ((S1 & S0) ? X3 :
             (S1 & ~S0) ? X2 :
             (~S1 & S0) ? X1 :
             X0) ) )
    else $error("MUX_4to1: equation mismatch");

  // Coverage: hit all select cases with correct routing
  c_sel_00: cover property ( ({S1,S0}==2'b00) && (Y===X0) );
  c_sel_01: cover property ( ({S1,S0}==2'b01) && (Y===X1) );
  c_sel_10: cover property ( ({S1,S0}==2'b10) && (Y===X2) );
  c_sel_11: cover property ( ({S1,S0}==2'b11) && (Y===X3) );

endmodule

// Bind the checker to the DUT
bind MUX_4to1 MUX_4to1_sva MUX_4to1_sva_i (.*);