// SVA for mux_2to1
// Bind these assertions to the DUT.
module mux_2to1_sva (input logic in0, in1, sel, out);

  // Functional equivalence (4-state aware, includes X-propagation semantics of ?:)
  // Triggers on any relevant change.
  assert property (@(in0 or in1 or sel or out)
    out === (sel ? in1 : in0)
  ) else $error("mux_2to1: Functional mismatch");

  // Deterministic cases
  assert property (@(in0 or in1 or sel or out)
    (sel === 1'b0) |-> (out === in0)
  ) else $error("mux_2to1: sel=0 case failed");

  assert property (@(in0 or in1 or sel or out)
    (sel === 1'b1) |-> (out === in1)
  ) else $error("mux_2to1: sel=1 case failed");

  // X-propagation corner cases (when sel is X/Z)
  assert property (@(in0 or in1 or sel or out)
    ((sel !== 1'b0) && (sel !== 1'b1) && (in0 === in1)) |-> (out === in0)
  ) else $error("mux_2to1: sel=X and in0==in1 but out mismatched");

  assert property (@(in0 or in1 or sel or out)
    ((sel !== 1'b0) && (sel !== 1'b1) && (in0 !== in1)) |-> $isunknown(out)
  ) else $error("mux_2to1: sel=X and in0!=in1 but out not X");

  // Stability: unselected input changes must not affect out
  assert property (@(in0 or in1 or sel or out)
    (sel === 1'b0 && $stable(in0) && $stable(sel)) |-> $stable(out)
  ) else $error("mux_2to1: Out changed with sel=0 and in0 stable");

  assert property (@(in0 or in1 or sel or out)
    (sel === 1'b1 && $stable(in1) && $stable(sel)) |-> $stable(out)
  ) else $error("mux_2to1: Out changed with sel=1 and in1 stable");

  // Out should not be X when selected path is known
  assert property (@(in0 or in1 or sel or out)
    (sel === 1'b0 && !$isunknown(in0)) |-> !$isunknown(out)
  ) else $error("mux_2to1: Out X with sel=0 and in0 known");

  assert property (@(in0 or in1 or sel or out)
    (sel === 1'b1 && !$isunknown(in1)) |-> !$isunknown(out)
  ) else $error("mux_2to1: Out X with sel=1 and in1 known");

  // Functional coverage (concise, hits key scenarios)
  cover property (@(in0 or in1 or sel or out) sel === 1'b0 && in0 === 1'b0 && out === 1'b0);
  cover property (@(in0 or in1 or sel or out) sel === 1'b0 && in0 === 1'b1 && out === 1'b1);
  cover property (@(in0 or in1 or sel or out) sel === 1'b1 && in1 === 1'b0 && out === 1'b0);
  cover property (@(in0 or in1 or sel or out) sel === 1'b1 && in1 === 1'b1 && out === 1'b1);

  cover property (@(in0 or in1 or sel or out)
    (sel !== 1'b0 && sel !== 1'b1) && (in0 === in1) && (out === in0)
  );
  cover property (@(in0 or in1 or sel or out)
    (sel !== 1'b0 && sel !== 1'b1) && (in0 !== in1) && $isunknown(out)
  );

  // Covers that output responds to selected input toggles
  cover property (@(in0 or in1 or sel or out)
    (sel === 1'b0 && $changed(in0) && $changed(out))
  );
  cover property (@(in0 or in1 or sel or out)
    (sel === 1'b1 && $changed(in1) && $changed(out))
  );

endmodule

bind mux_2to1 mux_2to1_sva sva_mux_2to1 (.*);