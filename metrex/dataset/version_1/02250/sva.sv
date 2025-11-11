// SVA bind file for xor_gate/functional_module/control_logic/top_module

// xor_gate assertions and coverage
module xor_gate_sva(input a, input b, input xor_out);
  // Functional equivalence when inputs are known
  property p_xor_correct;
    @(a or b or xor_out) disable iff ($isunknown({a,b}))
      xor_out === (a ^ b);
  endproperty
  assert property (p_xor_correct) else $error("xor_gate: xor_out != a^b");

  // Truth table coverage (when all known)
  cover property (@(a or b or xor_out) (! $isunknown({a,b,xor_out}) && a==0 && b==0 && xor_out==0));
  cover property (@(a or b or xor_out) (! $isunknown({a,b,xor_out}) && a==0 && b==1 && xor_out==1));
  cover property (@(a or b or xor_out) (! $isunknown({a,b,xor_out}) && a==1 && b==0 && xor_out==1));
  cover property (@(a or b or xor_out) (! $isunknown({a,b,xor_out}) && a==1 && b==1 && xor_out==0));
endmodule
bind xor_gate xor_gate_sva xor_gate_sva_i (.*);

// functional_module assertions and coverage
module functional_module_sva(input xor_out, input func_out);
  // Pass-through behavior when input known
  property p_func_passthru;
    @(xor_out or func_out) disable iff ($isunknown(xor_out))
      func_out === xor_out;
  endproperty
  assert property (p_func_passthru) else $error("functional_module: func_out != xor_out");

  // Output value coverage when known
  cover property (@(xor_out or func_out) (! $isunknown({xor_out,func_out}) && func_out==0));
  cover property (@(xor_out or func_out) (! $isunknown({xor_out,func_out}) && func_out==1));
endmodule
bind functional_module functional_module_sva functional_module_sva_i (.*);

// control_logic assertions and coverage
module control_logic_sva(
  input a, input b, input select, input out,
  input xor_out, input func_out
);
  // MUX correctness when all selects/inputs known
  property p_mux_correct;
    @(a or b or select or xor_out or func_out or out)
      disable iff ($isunknown({select,func_out,xor_out}))
      out === (select ? func_out : xor_out);
  endproperty
  assert property (p_mux_correct) else $error("control_logic: MUX select/out mismatch");

  // Each branch selected at least once (when known)
  cover property (@(select or out or func_out) (! $isunknown({select,func_out,out}) && (select==1) && (out===func_out)));
  cover property (@(select or out or xor_out ) (! $isunknown({select,xor_out ,out}) && (select==0) && (out===xor_out )));
endmodule
bind control_logic control_logic_sva control_logic_sva_i (
  .a(a), .b(b), .select(select), .out(out),
  .xor_out(xor_out), .func_out(func_out)
);

// top_module end-to-end assertions and coverage
module top_module_sva(input a, input b, input select, input out);
  // End-to-end: out must be XOR of a and b when inputs known
  property p_top_end_to_end;
    @(a or b or select or out) disable iff ($isunknown({a,b}))
      out === (a ^ b);
  endproperty
  assert property (p_top_end_to_end) else $error("top_module: out != a^b");

  // Input-space coverage (all 8 combinations of a,b,select when known)
  cover property (@(a or b or select) (! $isunknown({a,b,select}) && a==0 && b==0 && select==0));
  cover property (@(a or b or select) (! $isunknown({a,b,select}) && a==0 && b==0 && select==1));
  cover property (@(a or b or select) (! $isunknown({a,b,select}) && a==0 && b==1 && select==0));
  cover property (@(a or b or select) (! $isunknown({a,b,select}) && a==0 && b==1 && select==1));
  cover property (@(a or b or select) (! $isunknown({a,b,select}) && a==1 && b==0 && select==0));
  cover property (@(a or b or select) (! $isunknown({a,b,select}) && a==1 && b==0 && select==1));
  cover property (@(a or b or select) (! $isunknown({a,b,select}) && a==1 && b==1 && select==0));
  cover property (@(a or b or select) (! $isunknown({a,b,select}) && a==1 && b==1 && select==1));
endmodule
bind top_module top_module_sva top_module_sva_i (.*);