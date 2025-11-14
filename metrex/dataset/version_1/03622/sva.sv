// SVA checker for mux2to1
module mux2to1_sva (input logic a, b, sel, out);

  // Functional equivalence to RTL (includes 4-state semantics)
  always @* assert (#0 (out === ((sel == 1'b1) ? a : b)))
    else $error("mux2to1 mismatch: sel=%b a=%b b=%b out=%b", sel, a, b, out);

  // Strong checks when select is known
  ap_sel1: assert property (@(a or b or sel or out) (sel === 1'b1) |-> ##0 (out === a));
  ap_sel0: assert property (@(a or b or sel or out) (sel === 1'b0) |-> ##0 (out === b));

  // Out must not be X when selected input is known
  ap_no_x_a: assert property (@(a or b or sel or out) (sel === 1'b1 && !$isunknown(a)) |-> ##0 !$isunknown(out));
  ap_no_x_b: assert property (@(a or b or sel or out) (sel === 1'b0 && !$isunknown(b)) |-> ##0 !$isunknown(out));

  // X/Z select behavior matches ternary semantics
  ap_selx_equal:   assert property (@(a or b or sel or out) (sel !== 1'b0 && sel !== 1'b1 && (a === b)) |-> ##0 (out === a));
  ap_selx_unequal: assert property (@(a or b or sel or out) (sel !== 1'b0 && sel !== 1'b1 && (a !== b)) |-> ##0 $isunknown(out));

  // Coverage
  cp_sel_0_to_1: cover property (@(sel) sel === 1'b0 ##1 sel === 1'b1);
  cp_sel_1_to_0: cover property (@(sel) sel === 1'b1 ##1 sel === 1'b0);
  cp_route_a:    cover property (@(a or sel or out) (sel === 1'b1 && $changed(a)) ##0 (out === a));
  cp_route_b:    cover property (@(b or sel or out) (sel === 1'b0 && $changed(b)) ##0 (out === b));
  cp_selx_case:  cover property (@(a or b or sel or out) (sel !== 1'b0 && sel !== 1'b1) ##0 ((a===b && out===a) || (a!==b && $isunknown(out))));
endmodule

// Bind into DUT
bind mux2to1 mux2to1_sva sva_inst (.*);