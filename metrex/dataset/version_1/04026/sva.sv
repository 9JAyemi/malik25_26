// SVA for mux_2to1 — concise, high-quality checks and coverage
module mux_2to1_sva (input logic a, b, sel, out);
  // Sample on any relevant activity
  default clocking cb @(a or b or sel or out); endclocking

  // Combinational equivalence (4-state aware)
  assert property (out === ((~sel & a) | (sel & b)))
    else $error("mux_2to1: out != (~sel & a) | (sel & b)");

  // Determinism: known inputs imply known output
  assert property ((!$isunknown({a,b,sel})) |-> (!$isunknown(out)))
    else $error("mux_2to1: inputs known but out is X/Z");

  // No spurious output toggle
  assert property ($changed(out) |-> ($changed(a) || $changed(b) || $changed(sel)))
    else $error("mux_2to1: out changed without a/b/sel change");

  // Unselected input must not affect output
  assert property ((sel===1'b0 && !$changed(sel) && $changed(b)) |-> !$changed(out))
    else $error("mux_2to1: b changed while sel=0, out glitched");
  assert property ((sel===1'b1 && !$changed(sel) && $changed(a)) |-> !$changed(out))
    else $error("mux_2to1: a changed while sel=1, out glitched");

  // Selected input drives output immediately
  assert property ((sel===1'b0 && !$changed(sel) && $changed(a)) |-> (out===a))
    else $error("mux_2to1: a change not reflected when sel=0");
  assert property ((sel===1'b1 && !$changed(sel) && $changed(b)) |-> (out===b))
    else $error("mux_2to1: b change not reflected when sel=1");

  // Select transitions land on the correct source
  assert property ($rose(sel) |-> (out===b))
    else $error("mux_2to1: after sel rise, out != b");
  assert property ($fell(sel) |-> (out===a))
    else $error("mux_2to1: after sel fall, out != a");

  // Functional coverage: both paths, transitions, and data propagation
  cover property (sel===1'b0 && out===a);
  cover property (sel===1'b1 && out===b);
  cover property ($rose(sel));
  cover property ($fell(sel));
  cover property (sel===1'b0 && $changed(a) && out===a);
  cover property (sel===1'b1 && $changed(b) && out===b);
endmodule

// Bind to DUT
bind mux_2to1 mux_2to1_sva mux_2to1_sva_i (.*);