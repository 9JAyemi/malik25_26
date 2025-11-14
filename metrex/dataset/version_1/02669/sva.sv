// SVA for mux2to1
// Bind this to the DUT: bind mux2to1 mux2to1_sva i_mux2to1_sva(.*);

module mux2to1_sva (input a, b, sel, out);

  default clocking cb @(*); endclocking

  // Functional correctness (combinational, zero-delay)
  property p_sel0;    (sel === 1'b0) |-> ##0 (out === a); endproperty
  property p_sel1;    (sel === 1'b1) |-> ##0 (out === b); endproperty
  assert property (p_sel0);
  assert property (p_sel1);

  // X-prop semantics of ?: when sel is X/Z
  property p_selx_diff; (sel !== 1'b0 && sel !== 1'b1 && (a !== b)) |-> ##0 (out === 1'bx); endproperty
  property p_selx_same; (sel !== 1'b0 && sel !== 1'b1 && (a === b)) |-> ##0 (out === a);   endproperty
  assert property (p_selx_diff);
  assert property (p_selx_same);

  // No X on out when selected input is known
  assert property ((sel === 1'b0 && !$isunknown(a)) |-> ##0 !$isunknown(out));
  assert property ((sel === 1'b1 && !$isunknown(b)) |-> ##0 !$isunknown(out));

  // Isolation: unselected input toggles do not affect out
  assert property ((sel === 1'b0 && $changed(b) && $stable(sel) && $stable(a)) |-> ##0 $stable(out));
  assert property ((sel === 1'b1 && $changed(a) && $stable(sel) && $stable(b)) |-> ##0 $stable(out));

  // Propagation: selected input changes reflect immediately on out
  assert property ((sel === 1'b0 && $changed(a) && $stable(sel)) |-> ##0 (out === a));
  assert property ((sel === 1'b1 && $changed(b) && $stable(sel)) |-> ##0 (out === b));

  // Coverage
  cover property (sel === 1'b0 && out === a);
  cover property (sel === 1'b1 && out === b);
  cover property ($rose(a) && sel === 1'b0 && out === a);
  cover property ($rose(b) && sel === 1'b1 && out === b);
  cover property ($fell(a) && sel === 1'b0 && out === a);
  cover property ($fell(b) && sel === 1'b1 && out === b);
  cover property ($changed(sel));

endmodule