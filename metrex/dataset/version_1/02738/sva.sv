// SVA for mux_2to1
// Bind this checker to the DUT instance
module mux_2to1_sva (
  input logic a,
  input logic b,
  input logic sel,
  input logic out
);

  // Golden 4-state mux behavior
  function automatic logic exp_mux (input logic a_i, b_i, sel_i);
    if (sel_i === 1'b0)      exp_mux = a_i;
    else if (sel_i === 1'b1) exp_mux = b_i;
    else if (a_i === b_i)    exp_mux = a_i;
    else                     exp_mux = 1'bx;
  endfunction

  // Core functional equivalence (including X semantics); sample on any relevant change
  property p_func;
    @(a or b or sel or out) 1'b1 |-> ##0 (out === exp_mux(a,b,sel));
  endproperty
  assert property (p_func);

  // X-propagation: unknown sel with differing inputs must yield unknown out
  property p_xprop;
    @(a or b or sel or out)
      ((sel !== 1'b0) && (sel !== 1'b1) && (a !== b)) |-> ##0 (out !== 1'b0 && out !== 1'b1);
  endproperty
  assert property (p_xprop);

  // Stability: with fixed select, out cannot change unless the selected input changes
  property p_stable_a;
    @(a or b or sel or out)
      (sel === 1'b0 && !$changed(sel) && !$changed(a)) |-> ##0 !$changed(out);
  endproperty
  assert property (p_stable_a);

  property p_stable_b;
    @(a or b or sel or out)
      (sel === 1'b1 && !$changed(sel) && !$changed(b)) |-> ##0 !$changed(out);
  endproperty
  assert property (p_stable_b);

  // Coverage: all select/data/output combinations and key behaviors
  cover property (@(a or b or sel or out) sel===1'b0 && a===1'b0 ##0 out===1'b0);
  cover property (@(a or b or sel or out) sel===1'b0 && a===1'b1 ##0 out===1'b1);
  cover property (@(a or b or sel or out) sel===1'b1 && b===1'b0 ##0 out===1'b0);
  cover property (@(a or b or sel or out) sel===1'b1 && b===1'b1 ##0 out===1'b1);
  cover property (@(a or b or sel or out) (sel !== 1'b0 && sel !== 1'b1) && (a !== b) ##0 (out !== 1'b0 && out !== 1'b1));
  cover property (@(a or b or sel or out) (sel !== 1'b0 && sel !== 1'b1) && (a === b) ##0 (out === a));
  cover property (@(a or b or sel or out) sel===1'b0 && $changed(a) ##0 $changed(out));
  cover property (@(a or b or sel or out) sel===1'b1 && $changed(b) ##0 $changed(out));

endmodule

bind mux_2to1 mux_2to1_sva mux_2to1_sva_i (.a(a), .b(b), .sel(sel), .out(out));