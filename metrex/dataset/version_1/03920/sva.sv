// SVA for logic_module
// Concise, high-quality functional checks and coverage

// synthesis translate_off
module logic_module_sva (
  input logic a, b,
  input logic g_out, p_out,
  input logic n2
);
  // Sample on any input edge; check after delta (##0) to avoid race
  default clocking cb @(posedge a or negedge a or posedge b or negedge b); endclocking

  // Functional correctness
  property comb_correct;
    1 |-> ##0 ((n2 == ~a) && (g_out == (a & b)) && (p_out == (a ^ b)));
  endproperty
  assert property (comb_correct);

  // No X/Z on internal/output nets
  assert property (1 |-> ##0 !$isunknown({n2, g_out, p_out}));

  // Truth table coverage
  cover property (1 |-> ##0 (a==0 && b==0 && g_out==0 && p_out==0));
  cover property (1 |-> ##0 (a==0 && b==1 && g_out==0 && p_out==1));
  cover property (1 |-> ##0 (a==1 && b==0 && g_out==0 && p_out==1));
  cover property (1 |-> ##0 (a==1 && b==1 && g_out==1 && p_out==0));

  // Toggle coverage
  cover property ($rose(g_out));
  cover property ($fell(g_out));
  cover property ($rose(p_out));
  cover property ($fell(p_out));
endmodule

bind logic_module logic_module_sva (.*);
// synthesis translate_on