// SVA for majority_gate: bind-in module with concise, high-quality checks and coverage

`define ANYEDGE (posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)

module majority_gate_sva;
  // Functional correctness: 2-of-4 threshold behavior
  property p_func_2of4;
    @(`ANYEDGE) !$isunknown({A,B,C,D}) |-> ( X == ($countones({A,B,C,D}) >= 2) );
  endproperty
  assert property (p_func_2of4);

  // Internal consistency against ports (no dependency on internal wires)
  property p_mj1_from_ports;
    @(`ANYEDGE) !$isunknown({A,B,C,D}) |-> ( majority1 == ((A&B)|(A&C)|(A&D)|(B&C)|(B&D)|(C&D)) );
  endproperty
  assert property (p_mj1_from_ports);

  property p_mj0_from_ports;
    @(`ANYEDGE) !$isunknown({A,B,C,D}) |-> ( majority0 == ~((A&B)|(A&C)|(A&D)|(B&C)|(B&D)|(C&D)) );
  endproperty
  assert property (p_mj0_from_ports);

  // Output combines the two internal majorities as coded
  property p_out_from_internals;
    @(`ANYEDGE) !$isunknown({A,B,C,D}) |-> ( X == (majority1 & ~majority0) );
  endproperty
  assert property (p_out_from_internals);

  // No X/Z propagation when inputs are known
  property p_no_xprop;
    @(`ANYEDGE) !$isunknown({A,B,C,D}) |-> !$isunknown(X);
  endproperty
  assert property (p_no_xprop);

  // Coverage: all cardinalities and threshold crossings
  cover property (@(`ANYEDGE) !$isunknown({A,B,C,D,X}) && ($countones({A,B,C,D})==0) && (X==0));
  cover property (@(`ANYEDGE) !$isunknown({A,B,C,D,X}) && ($countones({A,B,C,D})==1) && (X==0));
  cover property (@(`ANYEDGE) !$isunknown({A,B,C,D,X}) && ($countones({A,B,C,D})==2) && (X==1));
  cover property (@(`ANYEDGE) !$isunknown({A,B,C,D,X}) && ($countones({A,B,C,D})==3) && (X==1));
  cover property (@(`ANYEDGE) !$isunknown({A,B,C,D,X}) && ($countones({A,B,C,D})==4) && (X==1));

  // Threshold transitions (ensure both edges are exercised)
  cover property (@(`ANYEDGE)
                  !$isunknown({A,B,C,D,X}) &&
                  !$isunknown($past({A,B,C,D,X})) &&
                  ($past($countones({A,B,C,D})) <= 1) &&
                  ($countones({A,B,C,D}) >= 2) && $rose(X));

  cover property (@(`ANYEDGE)
                  !$isunknown({A,B,C,D,X}) &&
                  !$isunknown($past({A,B,C,D,X})) &&
                  ($past($countones({A,B,C,D})) >= 2) &&
                  ($countones({A,B,C,D}) <= 1) && $fell(X));
endmodule

bind majority_gate majority_gate_sva sva_check();