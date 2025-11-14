// SVA for xor_gate and top_module (bindable, clockless)

module xor_gate_sva(input a, input b, input out);
  // Functional correctness when inputs are known
  property p_func;
    @(a or b or out) (!$isunknown({a,b})) |-> ##0 (out == (a ^ b));
  endproperty
  a_func: assert property(p_func);

  // Output must be known when inputs are known
  property p_known_out;
    @(a or b or out) (!$isunknown({a,b})) |-> ##0 (!$isunknown(out));
  endproperty
  a_known_out: assert property(p_known_out);

  // Functional coverage of all input combos with correct output
  cover property (@(a or b) ##0 (a==0 && b==0 && out==0));
  cover property (@(a or b) ##0 (a==0 && b==1 && out==1));
  cover property (@(a or b) ##0 (a==1 && b==0 && out==1));
  cover property (@(a or b) ##0 (a==1 && b==1 && out==0));
endmodule

bind xor_gate xor_gate_sva xor_gate_sva_i (.a(a), .b(b), .out(out));


module top_module_sva(input a, input b, input out_behavioral, input out_structural);
  // Functional correctness when inputs are known
  property p_func_beh;
    @(a or b or out_behavioral) (!$isunknown({a,b})) |-> ##0 (out_behavioral == (a ^ b));
  endproperty
  a_func_beh: assert property(p_func_beh);

  property p_func_str;
    @(a or b or out_structural) (!$isunknown({a,b})) |-> ##0 (out_structural == (a ^ b));
  endproperty
  a_func_str: assert property(p_func_str);

  // Equivalence (when inputs are known)
  property p_equiv;
    @(a or b or out_behavioral or out_structural)
      (!$isunknown({a,b})) |-> ##0 (out_behavioral == out_structural);
  endproperty
  a_equiv: assert property(p_equiv);

  // Outputs must be known when inputs are known
  property p_known_outs;
    @(a or b or out_behavioral or out_structural)
      (!$isunknown({a,b})) |-> ##0 (!$isunknown({out_behavioral,out_structural}));
  endproperty
  a_known_outs: assert property(p_known_outs);

  // Functional coverage of all input combos with both outputs correct
  cover property (@(a or b) ##0 (a==0 && b==0 && out_behavioral==0 && out_structural==0));
  cover property (@(a or b) ##0 (a==0 && b==1 && out_behavioral==1 && out_structural==1));
  cover property (@(a or b) ##0 (a==1 && b==0 && out_behavioral==1 && out_structural==1));
  cover property (@(a or b) ##0 (a==1 && b==1 && out_behavioral==0 && out_structural==0));

  // Edge coverage on both outputs
  cover property (@(a or b or out_behavioral) $rose(out_behavioral));
  cover property (@(a or b or out_behavioral) $fell(out_behavioral));
  cover property (@(a or b or out_structural) $rose(out_structural));
  cover property (@(a or b or out_structural) $fell(out_structural));
endmodule

bind top_module top_module_sva top_module_sva_i (.a(a), .b(b), .out_behavioral(out_behavioral), .out_structural(out_structural));