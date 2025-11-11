// SVA checker for my_module
module my_module_sva(input logic X, A1, A2, A3, B1);

  // Sampling on any edge of inputs or X
  `define COMB_EVT (posedge A1 or negedge A1 or \
                     posedge A2 or negedge A2 or \
                     posedge A3 or negedge A3 or \
                     posedge B1 or negedge B1 or \
                     posedge X  or negedge X)

  // Helper terms (product terms of the function)
  wire t1 = (A1 & ~A2);
  wire t2 = (A2 & ~A1 & A3 & ~B1);
  wire t3 = (~A1 & ~A2 & ~A3 & B1);

  // Functional equivalence: when inputs are known, X must equal the Boolean expression
  property p_func_eq;
    !$isunknown({A1,A2,A3,B1}) |-> (X === (t1 | t2 | t3));
  endproperty
  assert property (@(`COMB_EVT) p_func_eq)
    else $error("my_module: X != expected Boolean function");

  // Output known when inputs known
  property p_no_xz_out_when_inputs_known;
    !$isunknown({A1,A2,A3,B1}) |-> !$isunknown(X);
  endproperty
  assert property (@(`COMB_EVT) p_no_xz_out_when_inputs_known)
    else $error("my_module: X is X/Z while inputs are known");

  // Mutually exclusive product terms (sanity of expression structure)
  property p_terms_mut_excl;
    !$isunknown({A1,A2,A3,B1}) |-> !(t1 & t2) && !(t1 & t3) && !(t2 & t3);
  endproperty
  assert property (@(`COMB_EVT) p_terms_mut_excl)
    else $error("my_module: overlapping product terms detected");

  // Coverage: hit each product term causing X=1
  cover property (@(`COMB_EVT) (!$isunknown({A1,A2,A3,B1})) && t1 && (X==1));
  cover property (@(`COMB_EVT) (!$isunknown({A1,A2,A3,B1})) && t2 && (X==1));
  cover property (@(`COMB_EVT) (!$isunknown({A1,A2,A3,B1})) && t3 && (X==1));

  // Coverage: none of the terms true -> X==0
  cover property (@(`COMB_EVT) (!$isunknown({A1,A2,A3,B1})) && !(t1|t2|t3) && (X==0));

  // Coverage: observe both edges on X under known inputs
  cover property (@(`COMB_EVT) (!$isunknown({A1,A2,A3,B1})) && $rose(X));
  cover property (@(`COMB_EVT) (!$isunknown({A1,A2,A3,B1})) && $fell(X));

  `undef COMB_EVT
endmodule

// Bind the checker to the DUT
bind my_module my_module_sva u_my_module_sva (.*);