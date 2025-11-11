// SVA for mux_2to1
module mux_2to1_sva(input logic a, b, sel, out);

  // Sample on any input change
  default clocking cb @(posedge a or negedge a or posedge b or negedge b or posedge sel or negedge sel); endclocking

  // Functional equivalence (4-state correct)
  property p_equiv; out === (sel ? b : a); endproperty
  assert property (p_equiv);

  // X/Z behavior when sel is unknown
  assert property (($isunknown(sel) && (a !== b)) |-> $isunknown(out));
  assert property (($isunknown(sel) && (a === b)) |-> (out === a));

  // If sel and selected input are known, out must be known
  assert property ((((sel === 1'b0) && !$isunknown(a)) ||
                    ((sel === 1'b1) && !$isunknown(b))) |-> !$isunknown(out));

  // Coverage: each path/value and X-cases
  cover property (sel===1'b0 && a===1'b0 && out===1'b0);
  cover property (sel===1'b0 && a===1'b1 && out===1'b1);
  cover property (sel===1'b1 && b===1'b0 && out===1'b0);
  cover property (sel===1'b1 && b===1'b1 && out===1'b1);
  cover property ($isunknown(sel) && (a===b) && (out===a));
  cover property ($isunknown(sel) && (a!==b) && $isunknown(out));

endmodule

// Bind into the DUT
bind mux_2to1 mux_2to1_sva mux_2to1_sva_i(.a(a), .b(b), .sel(sel), .out(out));