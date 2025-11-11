// SVA checker for state_module
// Bind this to the DUT; focuses on concise, high-quality checks and coverage
module state_module_sva (
  input logic g, p, g_prec, p_prec,
  input logic g_out, p_out
);

  // Drive a combinational sampling event on any relevant change
  event comb_ev;
  logic [5:0] sens;
  always @* begin
    sens = {g,p,g_prec,p_prec,g_out,p_out};
    -> comb_ev;
  end

  // Restrict inputs to 0/1 to avoid X/Z ambiguity; then outputs must be known
  assume property (@(comb_ev) !$isunknown({g,p,g_prec,p_prec}));
  assert property (@(comb_ev) !$isunknown({g_out,p_out}));

  // Functional equivalence
  assert property (@(comb_ev) g_out == (p | (g_prec & ~p_prec)));
  assert property (@(comb_ev) p_out == (p & p_prec));

  // Key implications and independence from unused input g
  assert property (@(comb_ev) p |-> g_out);
  assert property (@(comb_ev) (!p && p_prec) |-> !g_out);
  assert property (@(comb_ev) (!p && !p_prec) |-> (g_out == g_prec));
  assert property (@(comb_ev) $changed(g) && $stable({p,g_prec,p_prec}) |-> $stable({g_out,p_out}));

  // Coverage: exercise distinct functional regions and toggles
  cover property (@(comb_ev) p);                                  // g_out via p
  cover property (@(comb_ev) (!p && !p_prec && g_prec));          // g_out via g_prec
  cover property (@(comb_ev) (!p && !p_prec && !g_prec));         // g_out low via g_prec=0
  cover property (@(comb_ev) (!p && p_prec));                     // g_out forced low by p_prec
  cover property (@(comb_ev) (p && p_prec && g_out && p_out));    // both outputs high
  cover property (@(comb_ev) (!p && p_prec && !g_out && !p_out)); // both outputs low
  cover property (@(comb_ev) $rose(g_out));
  cover property (@(comb_ev) $fell(g_out));
  cover property (@(comb_ev) $rose(p_out));
  cover property (@(comb_ev) $fell(p_out));

endmodule

bind state_module state_module_sva sva_i (.*);