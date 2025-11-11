// SVA for mux2to1
module mux2to1_sva(input logic in0, in1, sel, out);

  // Functional correctness (4-state accurate)
  assert property (@(in0 or in1 or sel)
                   out === (sel ? in1 : in0));

  // Output only changes if an input or select changes (no spontaneous toggles)
  assert property (@(in0 or in1 or sel or out)
                   $changed(out) |-> ($changed(sel) || $changed(in0) || $changed(in1)));

  // If select and chosen input are known, output must be known
  assert property (@(in0 or in1 or sel)
                   (sel === 1'b0 && !$isunknown(in0)) |-> !$isunknown(out));
  assert property (@(in0 or in1 or sel)
                   (sel === 1'b1 && !$isunknown(in1)) |-> !$isunknown(out));

  // Equal inputs force deterministic output regardless of sel (even if sel is X/Z)
  assert property (@(in0 or in1 or sel)
                   (!$isunknown(in0) && in0 === in1) |-> (out === in0));

  // Optional: flag unknown select
  assert property (@(sel) !$isunknown(sel));

  // Coverage: exercise both data paths and propagation on changes
  cover property (@(in0 or in1 or sel) (sel === 1'b0 && out === in0));
  cover property (@(in0 or in1 or sel) (sel === 1'b1 && out === in1));
  cover property (@(posedge sel) out === in1);
  cover property (@(negedge sel) out === in0);
  cover property (@(in0) (sel === 1'b0) && $changed(out));
  cover property (@(in1) (sel === 1'b1) && $changed(out));
  cover property (@(in0 or in1 or sel)
                  ($isunknown(sel) && in0 === in1 && !$isunknown(in0) && out === in0));

endmodule

bind mux2to1 mux2to1_sva sva_mux2to1 (.*);